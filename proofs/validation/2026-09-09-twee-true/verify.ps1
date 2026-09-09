$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../../..')).Path
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'manifest.json') -Raw | ConvertFrom-Json
if ($manifest.entries.Count -ne 2) { throw 'Expected exactly two true certificates' }
$checked = 0
$index = Get-Content -LiteralPath (Join-Path $repoRoot 'proofs/index.json') -Raw | ConvertFrom-Json
foreach ($entry in $manifest.entries) {
  if ($entry.eq1_id -notin @(5834,40037) -or $entry.eq2_id -ne 2 -or $entry.verdict -ne 'true') { throw 'Wrong implication' }
  foreach ($file in $entry.files) {
    $path = Join-Path $repoRoot $file.path
    if ((Get-Item -LiteralPath $path).Length -ne $file.bytes -or (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $file.sha256) { throw "Archive mismatch: $path" }
    $checked++
  }
  $dir = Join-Path $repoRoot ('proofs/Equation' + $entry.eq1_id)
  $receipt = Get-Content -LiteralPath (Join-Path $dir 'judge_acceptance.json') -Raw | ConvertFrom-Json
  $problem = Get-Content -LiteralPath (Join-Path $dir 'problem.json') -Raw | ConvertFrom-Json
  $certificate = @($entry.files | Where-Object { $_.path.EndsWith('/Triviality.lean') })
  if ($certificate.Count -ne 1 -or $receipt.record_kind -ne 'fresh_judge_v3_acceptance_excerpt' -or $receipt.status -ne 'accepted' -or $receipt.error_code -ne 'ACCEPTED' -or $receipt.verdict -ne 'true' -or $receipt.certificate_sha256 -ne $certificate[0].sha256 -or $receipt.certificate_bytes -ne $certificate[0].bytes) { throw 'Judge acceptance binding mismatch' }
  foreach ($field in @('id','eq1_id','eq2_id','equation1','equation2')) {
    if ($problem.$field -cne $receipt.problem.$field) { throw 'Problem receipt mismatch' }
  }
  if ($problem.eq1_id -ne $entry.eq1_id -or $problem.eq2_id -ne 2 -or $problem.equation2 -cne 'x = y') { throw 'Wrong exact target' }
  $payload = [ordered]@{eq1_id=$problem.eq1_id;eq2_id=$problem.eq2_id;equation1=$problem.equation1;equation2=$problem.equation2;id=$problem.id} | ConvertTo-Json -Compress
  $hash = [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData([Text.Encoding]::UTF8.GetBytes($payload))).ToLowerInvariant()
  if ($hash -ne $receipt.problem_sha256) { throw 'Canonical problem hash mismatch' }
  $code = [IO.File]::ReadAllText((Join-Path $dir 'Triviality.lean'))
  if ($code -match '\b(sorry|admit|axiom|grind)\b') { throw 'Unexpected proof token' }
  $module = [IO.File]::ReadAllText((Join-Path $dir 'JudgeProblem.lean'))
  if (-not $module.Contains($problem.equation1.Replace('*','◇')) -or -not $module.Contains('∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G') -or $module.Contains('[Finite')) { throw 'Incorrect reconstructed unrestricted goal' }
  $row = @($index.equations | Where-Object equation -eq ('Equation' + $entry.eq1_id))
  if ($row.Count -ne 1 -or $row[0].infinite_model_proof -or $row[0].austin_status -ne 'excluded_all_models_trivial' -or $row[0].unrestricted_triviality_proof.sha256 -ne $certificate[0].sha256) { throw 'Index classification mismatch' }
}
$candidates = @($index.equations | Where-Object table -eq '20.2')
$nontrivial = @($candidates | Where-Object infinite_model_proof)
$excluded = @($candidates | Where-Object unrestricted_triviality_proof)
if ($candidates.Count -ne 96 -or $nontrivial.Count -ne 56 -or $excluded.Count -ne 2) { throw 'Candidate inventory mismatch' }
Write-Output "PASS: $checked file hashes; 2 exact true Judge v3 accepted receipt bindings; no grind/sorry; Candidate-96 inventory 56 nontrivial + 2 excluded + 38 unclassified. This audit does not rerun Judge."
