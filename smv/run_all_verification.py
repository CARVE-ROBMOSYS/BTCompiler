# This document contains no USA or EU export controlled technical data.
#
# CARVE has received funding from the European Union's Horizon 2020 research
# and innovation programme under grant agreement No 732410, in the form of
# financial support to third parties of the RobMoSys project.

import unittest
import subprocess


class RunBTPropertiesVerification(unittest.TestCase):

    def _is_property_line(self, line):
        return line.startswith('-- ') and (line.endswith('true') or
                                           line.endswith('false'))

    def _run_nusmv(self, smv_file):
        # use 'universal_newlines' to create pipes in text mode.
        process = subprocess.Popen(['nuXmv', '-cpp', smv_file],
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE,
                                   universal_newlines=True)
        out, err = process.communicate()
        process.wait()
        # NuSMV does not seem to use its exit code to signal a failure in the
        # verificaiton of the properties.
        # We have to parse its output.
        print(smv_file + ':')
        for line in out.splitlines():
            if self._is_property_line(line):
                print('\t' + line)
                self.assertTrue(line.endswith('true'))

    def test_uc1_tick_props(self):
        self._run_nusmv('skill_test.smv')
        self._run_nusmv('skill_loop_test.smv')
        self._run_nusmv('sequence_test.smv')
        self._run_nusmv('sequence_loop_test.smv')
        self._run_nusmv('parallel_test.smv')
        self._run_nusmv('parallel_loop_test.smv')
        self._run_nusmv('uc1_single_tick.smv')
        self._run_nusmv('uc1.smv')
        self._run_nusmv('uc1_parallel.smv')
        self._run_nusmv('uc1_single_tick_ext.smv')
        self._run_nusmv('uc1_ext.smv')
        self._run_nusmv('uc1_parallel_ext.smv')
        self._run_nusmv('uc1_contract.smv')
        self._run_nusmv('with_memory.smv')
        self._run_nusmv('without_memory.smv')


if __name__ == '__main__':
    unittest.main()
