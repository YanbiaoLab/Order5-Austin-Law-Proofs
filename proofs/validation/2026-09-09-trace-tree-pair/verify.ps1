$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../../..')).Path
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'manifest.json') -Raw | ConvertFrom-Json
if ($manifest.entries.Count -ne 2) { throw 'Expected two archived equations' }
$checked = 0
foreach ($entry in $manifest.entries) {
  foreach ($file in $entry.files) {
    $path = Join-Path $repoRoot $file.path
    if ((Get-Item -LiteralPath $path).Length -ne $file.bytes -or (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $file.sha256) { throw "Archive mismatch: $path" }
    $checked++
  }
  $dir = Join-Path $repoRoot ('proofs/Equation' + $entry.eq1_id)
  $receipt = Get-Content -LiteralPath (Join-Path $dir 'judge_acceptance.json') -Raw | ConvertFrom-Json
  $problem = Get-Content -LiteralPath (Join-Path $dir 'problem.json') -Raw | ConvertFrom-Json
  $certificate = $entry.files | Where-Object { $_.path.EndsWith('/InfiniteModel.lean') }
  if ($receipt.eq1_id -ne $entry.eq1_id -or $receipt.eq2_id -ne 2 -or $receipt.status -ne 'accepted' -or $receipt.verdict -ne 'false' -or $receipt.certificate_sha256 -ne $certificate.sha256 -or $receipt.certificate_bytes -ne $certificate.bytes) { throw 'Historical certificate receipt mismatch' }
  if ($problem.eq1_id -ne $entry.eq1_id -or $problem.eq2_id -ne 2 -or $problem.id -ne $receipt.problem_id) { throw 'Problem ID mismatch' }
  $payload = [ordered]@{eq1_id=$problem.eq1_id;eq2_id=$problem.eq2_id;equation1=$problem.equation1;equation2=$problem.equation2;id=$problem.id} | ConvertTo-Json -Compress
  if ($payload -match '[^\x00-\x7F]') { throw 'Canonical payload must be ASCII' }
  $hash = [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData([Text.Encoding]::ASCII.GetBytes($payload))).ToLowerInvariant()
  if ($hash -ne $receipt.problem_sha256) { throw 'Released canonical problem hash mismatch' }
  $sourceEquation = $problem.equation1.Replace('*', '◇')
  if ($problem.equation2 -ne 'x = y') { throw 'Wrong target equation' }
  $expected = @"
import JudgeMagma.Magma

-- Reconstructed from the frozen paper input; not an archived Judge module.
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y z : G), $sourceEquation

@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x = y

abbrev Goal : Prop :=
  ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
"@
  $actual = [IO.File]::ReadAllText((Join-Path $dir 'JudgeProblem.lean'))
  if ($actual.Replace("`r`n", "`n").TrimEnd() -cne $expected.Replace("`r`n", "`n").TrimEnd()) { throw 'Reconstructed Lean goal mismatch' }
}
$index = Get-Content -LiteralPath (Join-Path $repoRoot 'proofs/index.json') -Raw | ConvertFrom-Json
$paper = @($manifest.paper_baseline_ids | Sort-Object -Unique)
$later = @($manifest.later_ids | Sort-Object -Unique)
if ($paper.Count -ne 32 -or $later.Count -ne 24 -or @($paper | Where-Object { $_ -in $later }).Count -ne 0) { throw 'Baseline/later count or overlap mismatch' }
$expectedIDs = @($paper + $later | Sort-Object -Unique)
$actualIDs = @($index.equations | Where-Object { $_.table -eq '20.2' -and $_.infinite_model_proof } | ForEach-Object { [int]($_.equation -replace '^Equation','') } | Sort-Object -Unique)
if (Compare-Object $expectedIDs $actualIDs) { throw 'Candidate-96 inventory mismatch' }
foreach ($row in $index.equations | Where-Object { $_.infinite_model_proof -and $_.equation -in @('Equation9680','Equation36524') }) {
  if ((Get-FileHash -LiteralPath (Join-Path $repoRoot $row.infinite_model_proof.path) -Algorithm SHA256).Hash.ToLowerInvariant() -ne $row.infinite_model_proof.sha256) { throw 'Index certificate hash mismatch' }
}
Write-Output "PASS: $checked file hashes, 2 historical accepted receipts, canonical problem hashes and reconstructed Lean goals; paper 32 + later 24 = 56 distinct Candidate-96 entries. No new Lean/Judge run."
