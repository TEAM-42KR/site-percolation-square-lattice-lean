import SitePerc.Checker.CompactCertificateBytesDefs

/-! Independent files share no decoder accumulator. Parallelizing their
materialization changes neither the actual decoder nor any output byte. -/
namespace SitePerc.Checker

def parallelDecodeFiles (files : Array (Array String)) : Array ByteArray := Id.run do
  let jobs := files.toList.map fun chunks =>
    Task.spawn (prio := Task.Priority.dedicated) fun _ =>
      CompactCertificateBytes.decodeChunks chunks
  return (jobs.map Task.get).toArray

end SitePerc.Checker
