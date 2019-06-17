import collections
import os.path as p
import subprocess
import sys
from config import IVERILOG_DIR, DEBUG


class Benchmark(collections.namedtuple("Benchmark",
                                       ["filename", "module", "annotfile"])):
    """
    Contains the information required to run a benchmark.
    """
    def run_iodine(self, extra_args=[], **kwargs):
        args = ["stack", "exec", "iodine", "--",
                "--iverilog-dir", IVERILOG_DIR]

        args.extend(extra_args)
        args.extend([p.realpath(self.filename),
                     self.module,
                     p.realpath(self.annotfile)])

        if DEBUG:
            print("running:\n{}".format(" ".join(args)),
                  file=sys.stderr)

        return subprocess.run(args, **kwargs).returncode

    def run_abduction(self):
        """ Run Iodine but with the abduction feature """
        return self.run_iodine(["--abduction"])

    def with_annot(self, annotfile):
        """ Returns a new benchmark with the given annotation file """
        return Benchmark(filename=self.filename,
                         module=self.module,
                         annotfile=annotfile)
