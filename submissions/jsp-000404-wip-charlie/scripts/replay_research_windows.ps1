param(
    [ValidateRange(1, 4)]
    [int] $Threads = 2,
    [switch] $SkipCache
)

# Research replay only. There is no completed original-problem root theorem.
# A successful module build must never be reported as solving JSP-000404.
$ErrorActionPreference = 'Stop'
# Keep a failing native build as a recorded check result, then continue to
# the separate admitted-root build and strict audit. This is script-local.
$PSNativeCommandUseErrorActionPreference = $false
$projectDirectory = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$previousThreads = $env:LEAN_NUM_THREADS
$failures = [System.Collections.Generic.List[string]]::new()
$successfulTargets = [System.Collections.Generic.HashSet[string]]::new()
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
    $upperProof = @($manifest.packages | Where-Object {
        $_.url -eq 'https://github.com/aznikline/jsp-000404-lean.git'
    })
    if ($upperProof.Count -ne 1 -or
        $upperProof[0].rev -ne 'cbfbbef188f5f98eead6045d7c3548de3c1b701a') {
        throw 'External sharpness proof does not match its audited immutable pin.'
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
        'JSP000404Research.ProjectionWholeCubeTQCanonicalOutwardOrder',
        'JSP000404Research.OriginalUpperBound'
    )
    foreach ($target in $targets) {
        $targetLog = Join-Path $logDirectory "$target.log"
        & lake build $target 2>&1 | Tee-Object -FilePath $targetLog
        $targetExit = $LASTEXITCODE
        "exit_code=$targetExit" | Add-Content -Encoding utf8 $targetLog
        if ($targetExit -ne 0) {
            $failures.Add($target)
        } else {
            [void] $successfulTargets.Add($target)
        }
    }

    # Audit only roots whose build passed in THIS replay. Otherwise an old
    # olean could give an irrelevant successful audit after a source failure.
    $generatorLog = Join-Path $logDirectory 'axiom-audit-generator.log'
    & python -B -X utf8 scripts/write_axiom_audits.py --output $logDirectory 2>&1 |
        Tee-Object -FilePath $generatorLog
    $generatorExit = $LASTEXITCODE
    "exit_code=$generatorExit" | Add-Content -Encoding utf8 $generatorLog
    if ($generatorExit -ne 0) {
        $failures.Add('axiom-audit-generator')
    } else {
        $audits = @(
            @{ Name = 'RootAxiomAudit'; Target = 'JSP000404Research' },
            @{ Name = 'AdmittedAxiomAudit'; Target = 'JSP000404Research.PlanarLowerBranchProofAdmittedWIP' }
        )
        foreach ($audit in $audits) {
            $axiomLog = Join-Path $logDirectory "$($audit.Name).log"
            if (-not $successfulTargets.Contains($audit.Target)) {
                'status=SKIPPED; corresponding build failed in this replay' |
                    Set-Content -Encoding utf8 $axiomLog
                $failures.Add($audit.Name)
                continue
            }
            $axiomSource = Join-Path $logDirectory "$($audit.Name).lean"
            & lake env lean $axiomSource 2>&1 | Tee-Object -FilePath $axiomLog
            $axiomExit = $LASTEXITCODE
            "exit_code=$axiomExit" | Add-Content -Encoding utf8 $axiomLog
            if ($axiomExit -ne 0) { $failures.Add($audit.Name) }
        }
    }

    $auditLog = Join-Path $logDirectory 'strict-sorry-audit.log'
    & python -B -X utf8 scripts/jsp000404_sorry_audit.py 2>&1 | Tee-Object -FilePath $auditLog
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
