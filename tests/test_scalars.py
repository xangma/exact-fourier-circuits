from fractions import Fraction
import json
import unittest

from exact_fourier.scalars import GaussianRational as QI, I, ONE, ZERO


class GaussianRationalTests(unittest.TestCase):
    def test_exact_field_arithmetic(self):
        a, b = QI(Fraction(2, 3), Fraction(-7, 5)), QI(Fraction(-9, 4), Fraction(1, 6))
        self.assertEqual(a + b - b, a)
        self.assertEqual(a * b / b, a)
        self.assertEqual(a * (b + I), a * b + a * I)
        self.assertEqual(I * I, -1)
        self.assertEqual((a + b).conjugate(), a.conjugate() + b.conjugate())
        self.assertEqual(a * a.conjugate(), a.norm_squared())

    def test_no_floating_point_coercion(self):
        for value in (0.1, complex(1, 2), True, None):
            with self.assertRaises(TypeError):
                QI.coerce(value)
        with self.assertRaises(TypeError):
            QI(1, 0.5)
        self.assertEqual(QI("0.1"), QI(Fraction(1, 10)))
        self.assertEqual(QI.coerce(("1/3", "2/7")), QI(Fraction(1, 3), Fraction(2, 7)))

    def test_integer_powers_and_zero(self):
        self.assertEqual(I ** 0, ONE)
        self.assertEqual(I ** 9, I)
        self.assertEqual(I ** -1, -I)
        self.assertEqual(QI(3, 4) ** -3 * QI(3, 4) ** 3, ONE)
        self.assertFalse(ZERO)
        self.assertTrue(I)
        with self.assertRaises(ZeroDivisionError):
            ONE / ZERO
        with self.assertRaises(ZeroDivisionError):
            ZERO ** -1
        with self.assertRaises(TypeError):
            I ** 0.5

    def test_json_roundtrip_and_canonical_fractions(self):
        scalar = QI(Fraction(14, 21), Fraction(-10, 15))
        self.assertEqual(scalar.to_dict(), {"real": [2, 3], "imag": [-2, 3]})
        self.assertEqual(QI.from_dict(json.loads(json.dumps(scalar.to_dict()))), scalar)
        self.assertEqual(QI.from_dict({"real": [4, 6], "imag": [0, 9]}), QI(Fraction(2, 3)))
        for value in ({"real": [0, 0], "imag": [0, 1]},
                      {"real": [True, 1], "imag": [0, 1]},
                      {"real": [1.0, 1], "imag": [0, 1]},
                      {"real": [1, -2], "imag": [0, 1]},
                      {"real": [1, 2]},
                      {"real": [1, 2], "imag": [0, 1], "extra": 1}):
            with self.assertRaises(ValueError):
                QI.from_dict(value)

    def test_real_hash_agrees_with_numeric_equality(self):
        self.assertEqual(QI(2), 2)
        self.assertEqual(hash(QI(2)), hash(2))
        self.assertEqual(hash(QI(Fraction(2, 3))), hash(Fraction(2, 3)))
        self.assertNotEqual(QI(2), "2")
        self.assertNotEqual(QI(0), False)


if __name__ == "__main__":
    unittest.main()
