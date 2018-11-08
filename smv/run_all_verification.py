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

    def _is_parse_error_line(self, line):
        return line.endswith(': Parser error')

    def _run_nusmv(self, smv_file):
        # use 'universal_newlines' to create pipes in text mode.
        process = subprocess.Popen(['nuXmv', '-cpp', smv_file],
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE,
                                   universal_newlines=True)
        out, err = process.communicate()
        print(smv_file + ':')
        process.wait()
        return out, err

    def _check_nuxmv_output_line(self, line):
        line = line.strip()
        if self._is_property_line(line):
            print(line)
            self.assertTrue(line.endswith('true'))

    def _parse_nuxmv_output(self, out):
        # NuSMV does not seem to use its exit code to signal a failure in the
        # verificaiton of the properties.  We have to parse its output.
        for line in out.splitlines():
            self._check_nuxmv_output_line(line)

    def _look_for_nuxmv_parse_errors(self, err):
        for line in err.splitlines():
            self.assertFalse(self._is_parse_error_line(line))

    def _run_smv_test(self, smv_file):
        out, err = self._run_nusmv(smv_file)
        # Parse errors are dumped to stderr instead of stdout.
        self._look_for_nuxmv_parse_errors(err)
        self._parse_nuxmv_output(out)

    def test_uc1_tick_props(self):
        self._run_smv_test('skill_test.smv')
        self._run_smv_test('skill_loop_test.smv')
        self._run_smv_test('sequence_test.smv')
        self._run_smv_test('sequence_loop_test.smv')
        self._run_smv_test('parallel_test.smv')
        self._run_smv_test('parallel_loop_test.smv')
        self._run_smv_test('uc1_single_tick.smv')
        self._run_smv_test('uc1.smv')
        self._run_smv_test('uc1_parallel.smv')
        self._run_smv_test('uc1_single_tick_ext.smv')
        self._run_smv_test('uc1_ext.smv')
        self._run_smv_test('uc1_parallel_ext.smv')
        self._run_smv_test('uc1_contract.smv')
        self._run_smv_test('with_memory.smv')
        self._run_smv_test('without_memory.smv')

    def test_bt_sequence(self):
        self._run_smv_test('test_bt_sequence.smv')
        self._run_smv_test('test_bt_with_reset_sequence.smv')
        self._run_smv_test('test_bt_sequence_with_memory.smv')

    def test_bt_fallback(self):
        self._run_smv_test('test_bt_fallback.smv')
        self._run_smv_test('test_bt_with_reset_fallback.smv')
        self._run_smv_test('test_bt_fallback_with_memory.smv')


if __name__ == '__main__':
    unittest.main()
