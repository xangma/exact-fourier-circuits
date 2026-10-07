"""CPU-only validation of the CUDA generator's exact gate/record contract."""

from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

try:
    import numpy as np
except ImportError:
    np = None

from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import KERNEL_C


spec = importlib.util.spec_from_file_location("projected_cuda", Path(__file__).resolve().parents[1] / "scripts/check-projected-cuda.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class ProjectedCudaContractTests(unittest.TestCase):
    def program(self):
        return {"schema": runner.SCHEMA,
                "metadata": {"roles": 8, "width": 4, "bank_size": 1, "original_roles": 6},
                "records": [[0, 0, 3, 0, 1, True], [1, 2, 4, -1, 2, False],
                            [2, 0, 1, 0, 1, False], [3, 3, 2, 0, 1, False],
                            [4, 0, 4, 0, 1, False]],
                "checkpoints": [{"label": "stage", "record_index": 2},
                                {"label": "final", "record_index": 5}]}

    def test_four_gate_pair_matches_exact_kernel(self):
        for x, y in ((QI(1), QI(0)), (QI(0), QI(1)), (QI(3, -7), QI(Fraction(2, 3), Fraction(-1, 9)))):
            expected = tuple(row[0] * x + row[1] * y for row in KERNEL_C)
            self.assertEqual(runner.exact_pair(x, y), expected)

    def test_actual_shear_word_restores_source_exactly(self):
        for coefficient in (Fraction(1), Fraction(-1), Fraction(1, 2), Fraction(-1, 2)):
            for y, x in ((QI(1), QI(0)), (QI(0), QI(1)), (QI(2, 7), QI(-3, 5))):
                self.assertEqual(runner.exact_compiled_shear(y, x, coefficient), (y + coefficient*x, x))
        code, descriptions = runner.shear_cases((Fraction(-1), Fraction(-1, 2), Fraction(1, 2), Fraction(1)))
        self.assertEqual(code.count("c_pair("), 12)
        self.assertTrue(all(item["C_calls"] == 3 for item in descriptions))
        self.assertTrue(all(item["scalar_gates"] == 4*3 + item["scalings"] for item in descriptions))

    def test_valid_record_and_checkpoint_contract(self):
        roles, width, coefficients, original, bank = runner.validate_program(self.program())
        self.assertEqual((roles, width, original, bank), (8, 4, 6, 1))
        self.assertEqual(coefficients, (Fraction(-1, 2),))
        source, _ = runner.cuda_source("float64", coefficients)
        self.assertIn("typedef double T", source)
        self.assertNotIn("@", source)
        self.assertIn("store_z(real,imag,second,x)", source)
        self.assertIn("__syncthreads()", source)

    def test_generated_cuda_tracking_needs_no_system_headers(self):
        for dtype in ("float32", "float64"):
            source, _ = runner.cuda_source(dtype, (Fraction(-1, 2), Fraction(1)))
            self.assertNotIn("#include", source)
            for function in ("isnan(", "isinf(", "fmax(", "fabs("):
                self.assertNotIn(function, source)
            self.assertIn("if(part!=part) nans++", source)
            self.assertIn("part>1.7976931348623157e308", source)
            self.assertIn("part<-1.7976931348623157e308", source)
            self.assertIn("if(magnitude>peak) peak=magnitude", source)

    def test_zero_directions_are_valid_identity_records(self):
        program = self.program()
        program["records"][0][2] = 0
        runner.validate_program(program)

    def test_bad_shapes_coordinates_coefficients_and_checkpoint_order(self):
        modifications = (("width", 3), ("roles", 7))
        for key, value in modifications:
            program = self.program()
            program["metadata"][key] = value
            with self.assertRaises(ValueError):
                runner.validate_program(program)
        for index, value in ((0, 5), (1, 8), (2, 4), (3, True), (4, 0), (5, 1)):
            program = self.program()
            program["records"][0][index] = value
            with self.assertRaises(ValueError):
                runner.validate_program(program)
        program = self.program()
        program["records"][1][3] = 0
        with self.assertRaises(ValueError):
            runner.validate_program(program)
        program = self.program()
        program["checkpoints"].reverse()
        with self.assertRaises(ValueError):
            runner.validate_program(program)

    def test_record_caps_fail_before_kernel_generation(self):
        with self.assertRaises(ValueError):
            runner.validate_program(self.program(), max_records=4)
        with self.assertRaises(ValueError):
            runner.validate_program(self.program(), max_width=2)

    @unittest.skipIf(np is None, "NumPy runtime unavailable")
    def test_fixture_shapes_and_finite_error_metrics(self):
        fixture = {key: np.zeros((2, 8, 4)) for key in ("real", "imag", "reference_real", "reference_imag")}
        fixture["family_names"] = np.array(("clean", "dirty"))
        fixture["checkpoint_reference_real"] = np.zeros((2, 2, 8, 4))
        fixture["checkpoint_reference_imag"] = np.zeros((2, 2, 8, 4))
        arrays, names = runner.normalize_fixture(fixture, 8, 4)
        self.assertEqual(names, ["clean", "dirty"])
        self.assertEqual(arrays["real"].shape, (2, 8, 4))
        result = runner.metrics(np.ones((8, 4)), np.zeros((8, 4)), np.ones((8, 4)), np.zeros((8, 4)))
        self.assertEqual(result["relative_l2"], 0)
        self.assertEqual(result["max_scaled_error"], 0)
        self.assertTrue(result["exact_reference_match"])
        result = runner.metrics(np.array((1.7e308,)), np.array((-1.7e308,)),
                                np.array((1.7e308,)), np.array((1.7e308,)))
        self.assertAlmostEqual(result["relative_l2"], 2 ** .5)
        self.assertEqual(result["nonfinite_elements"], 0)
        self.assertFalse(result["exact_reference_match"])
        self.assertEqual(result["error_evaluation"], "scaled-overflow-fallback")
        self.assertIsNone(result["max_absolute_error"])
        result = runner.metrics(np.array((float("inf"),)), np.array((float("nan"),)),
                                np.array((1.,)), np.array((0.,)))
        self.assertEqual(result["nonfinite_elements"], 1)
        self.assertIsNone(result["relative_l2"])

    @unittest.skipIf(np is None, "NumPy runtime unavailable")
    def test_one_ulp_discrepancy_survives_normalization(self):
        reference = np.array((3., 0.10084))
        observed = reference.copy()
        observed[1] = np.nextafter(reference[1], np.inf)
        # The old normalize-before-subtraction path erased this discrepancy.
        self.assertTrue(np.array_equal(observed / 3., reference / 3.))
        result = runner.metrics(observed, np.zeros(2), reference, np.zeros(2))
        self.assertFalse(result["exact_reference_match"])
        self.assertEqual(result["error_evaluation"], "raw-subtraction")
        self.assertEqual(result["max_absolute_error"], observed[1] - reference[1])
        self.assertGreater(result["relative_l2"], 0)
        self.assertGreater(result["max_scaled_error"], 0)

    @unittest.skipIf(np is None, "NumPy runtime unavailable")
    def test_subnormal_raw_difference_and_large_finite_ratio(self):
        least_positive = np.nextafter(0., 1.)
        result = runner.metrics(np.array((least_positive,)), np.zeros(1), np.zeros(1), np.zeros(1))
        self.assertFalse(result["exact_reference_match"])
        self.assertEqual(result["max_absolute_error"], least_positive)
        self.assertIsNone(result["relative_l2"])
        # Scale quotient alone would overflow, but the full norm ratio is finite.
        observed = np.zeros(1024)
        observed[0] = 1e308
        reference = np.full(1024, .1)
        result = runner.metrics(observed, np.zeros(1024), reference, np.zeros(1024))
        self.assertAlmostEqual(result["relative_l2"] / 1e308, 1 / 3.2)

    @unittest.skipIf(np is None, "NumPy runtime unavailable")
    def test_sweep_stops_after_first_execution_failure_and_retains_results(self):
        for failure in (subprocess.CompletedProcess([], 1, "", "compile failed"),
                        subprocess.TimeoutExpired([], 1, output=b"partial", stderr=b"timeout")):
            with self.subTest(failure=type(failure).__name__), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                program = folder / "program.json"
                program.write_text(json.dumps(self.program()))
                fixture = folder / "fixture.npz"
                np.savez(fixture, **{key: np.zeros((8, 4)) for key in
                                    ("real", "imag", "reference_real", "reference_imag")})
                prefix = folder / "results"
                arguments = ["check-projected-cuda.py", "--program", str(program), "--fixture", str(fixture),
                             "--output-prefix", str(prefix)]
                options = {"side_effect": failure} if isinstance(failure, Exception) else {"return_value": failure}
                with patch.object(runner.sys, "argv", arguments), patch.object(runner.subprocess, "run", **options) as launch:
                    with self.assertRaises(SystemExit) as exit_result:
                        runner.main()
                self.assertEqual(exit_result.exception.code, 1)
                self.assertEqual(launch.call_count, 1)
                aggregate = json.loads(Path(str(prefix) + ".results.json").read_text())
                self.assertEqual(len(aggregate["cases"]), 1)
                self.assertIn(aggregate["cases"][0]["status"], ("execution_error", "timeout"))


if __name__ == "__main__":
    unittest.main()
