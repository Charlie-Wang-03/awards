param(
    [ValidateRange(1, 4)]
    [int] $Threads = 2,
    [switch] $SkipCache
)

# Research replay only. There is no completed original-problem root theorem.
# A successful module build must never be reported as solving JSP-000404.
$ErrorActionPreference = 'Stop'
$projectDirectory = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$previousThreads = $env:LEAN_NUM_THREADS
$failures = [System.Collections.Generic.List[string]]::new()
Push-Location -LiteralPath $projectDirectory
try {
    $env:LEAN_NUM_THREADS = [string] $Threads
    $runStamp = [DateTime]::UtcNow.ToString('yyyyMMdd-HHmmss')
    $logDirectory = Join-Path $projectDirectory "artifacts/replay-$runStamp"
    New-Item -ItemType Directory -Path $logDirectory | Out-Null

    $toolchain = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    if ($toolchain -ne 'leanprover/lean4:v4.34.0') {
        throw "Unexpected toolchain: $toolchain"
    }
    $manifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $mathlib = @($manifest.packages | Where-Object { $_.name -eq 'mathlib' })
    if ($mathlib.Count -ne 1 -or
        $mathlib[0].rev -ne '5ed2965256430c3649e86755f9576b54eca72435') {
        throw 'Mathlib manifest does not match the audited research pin.'
    }

    $version = & lake --version 2>&1
    $versionExit = $LASTEXITCODE
    if ($versionExit -ne 0 -or "$version" -notmatch 'Lean version 4\.34\.0\)') {
        throw "Pinned Lake is unavailable: $version"
    }
    $metadata = @(
        "UTC=$([DateTime]::UtcNow.ToString('o'))"
        "project=$projectDirectory"
        "toolchain=$toolchain"
        "lake=$version"
        "LEAN_NUM_THREADS=$Threads"
        'status=INCOMPLETE; research replay, not a complete-proof certificate'
        "repository=$(& git rev-parse --show-toplevel)"
        "branch=$(& git branch --show-current)"
        "HEAD=$(& git rev-parse HEAD)"
        'working_tree_status:'
        (& git status --short)
        'remotes (read only):'
        (& git remote -v)
    )
    $metadata | Set-Content -Encoding utf8 (Join-Path $logDirectory 'environment.log')

    if (-not $SkipCache) {
        & lake exe cache get 2>&1 | Tee-Object -FilePath (Join-Path $logDirectory 'cache-get.log')
        $cacheExit = $LASTEXITCODE
        "exit_code=$cacheExit" | Add-Content -Encoding utf8 (Join-Path $logDirectory 'cache-get.log')
        if ($cacheExit -ne 0) { $failures.Add('cache-get') }
    }

    # Check both the umbrella and the admitted module: the latter is not in
    # the former's transitive imports. Never silently replace either target.
    $targets = @(
        'JSP000404Research',
        'JSP000404Research.PlanarLowerBranchProofAdmittedWIP',
        'JSP000404Research.ProjectionOrderCanonicalOrder',
        'JSP000404Research.ResidualQTTTCanonicalOrderRigidity',
        'JSP000404Research.ProjectionQTTTCanonicalOrderRigidity',
        'JSP000404Research.ProjectionWholeCubeTQCanonicalOutwardOrder'
    )
    foreach ($target in $targets) {
        $targetLog = Join-Path $logDirectory "$target.log"
        & lake build $target 2>&1 | Tee-Object -FilePath $targetLog
        $targetExit = $LASTEXITCODE
        "exit_code=$targetExit" | Add-Content -Encoding utf8 $targetLog
        if ($targetExit -ne 0) { $failures.Add($target) }
    }

    $auditLog = Join-Path $logDirectory 'strict-sorry-audit.log'
    & python -X utf8 scripts/jsp000404_sorry_audit.py 2>&1 | Tee-Object -FilePath $auditLog
    $auditExit = $LASTEXITCODE
    "exit_code=$auditExit" | Add-Content -Encoding utf8 $auditLog
    if ($auditExit -ne 0) { $failures.Add('strict-sorry-audit') }

    @(
        'status=INCOMPLETE'
        'No all-N original-problem theorem is certified by this script.'
        "failed_checks=$($failures -join ', ')"
    ) | Set-Content -Encoding utf8 (Join-Path $logDirectory 'result.log')
    Write-Output "Research evidence: $logDirectory"
    if ($failures.Count -gt 0) { exit 1 }
} finally {
    $env:LEAN_NUM_THREADS = $previousThreads
    Pop-Location
}
