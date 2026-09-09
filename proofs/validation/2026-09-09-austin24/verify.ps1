$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../../..')).Path
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'manifest.json') -Raw | ConvertFrom-Json
if ($manifest.entries.Count -ne 24) { throw 'Expected 24 entries' }
$checked = 0
foreach ($entry in $manifest.entries) {
  foreach ($file in $entry.files) {
    $path = Join-Path $repoRoot $file.path
    if ((Get-Item -LiteralPath $path).Length -ne $file.bytes) { throw "Size mismatch: $path" }
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $file.sha256) { throw "Hash mismatch: $path" }
    $checked++
  }
  $receiptFile = $entry.files | Where-Object { $_.path.EndsWith('/judge_acceptance.json') }
  $receipt = Get-Content -LiteralPath (Join-Path $repoRoot $receiptFile.path) -Raw | ConvertFrom-Json
  $model = $entry.files | Where-Object { $_.path.EndsWith('/InfiniteModel.lean') }
  if ($receipt.eq1_id -ne $entry.eq1_id -or $receipt.eq2_id -ne 2 -or $receipt.status -ne 'accepted' -or $receipt.error_code -ne 'ACCEPTED' -or $receipt.verdict -ne 'false' -or $receipt.certificate_sha256 -ne $model.sha256 -or $receipt.certificate_bytes -ne $model.bytes) {
    throw "Historical receipt mismatch: Equation$($entry.eq1_id)"
  }
}
Write-Output "PASS: 24 exact source/target IDs and historical accepted receipts; $checked file hashes. No new Lean/Judge run."
