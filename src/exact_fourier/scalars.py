"""Exact arithmetic in Q(i); no machine floating point enters this module."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise TypeError("exact components must be int, Fraction, or rational string")
    return Fraction(value)


def _decode_fraction(value: Any) -> Fraction:
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError("a rational component must be [numerator, denominator]")
    if any(isinstance(x, bool) or not isinstance(x, int) for x in value):
        raise ValueError("rational numerator and denominator must be integers")
    if value[1] <= 0:
        raise ValueError("rational denominator must be positive")
    return Fraction(value[0], value[1])


@dataclass(frozen=True, eq=False)
class GaussianRational:
    """An exact complex number ``real + imag*i`` with rational components."""

    real: Fraction = Fraction(0)
    imag: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "real", _fraction(self.real))
        object.__setattr__(self, "imag", _fraction(self.imag))

    @classmethod
    def coerce(cls, value: Any) -> GaussianRational:
        if isinstance(value, cls):
            return value
        if isinstance(value, (tuple, list)) and len(value) == 2:
            return cls(value[0], value[1])
        return cls(value)

    @classmethod
    def from_dict(cls, value: Any) -> GaussianRational:
        if not isinstance(value, dict) or set(value) != {"real", "imag"}:
            raise ValueError("a scalar must contain exactly real and imag")
        return cls(_decode_fraction(value["real"]), _decode_fraction(value["imag"]))

    def to_dict(self) -> dict[str, list[int]]:
        return {"real": [self.real.numerator, self.real.denominator],
                "imag": [self.imag.numerator, self.imag.denominator]}

    def __add__(self, other: Any) -> GaussianRational:
        other = self.coerce(other)
        return type(self)(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self) -> GaussianRational:
        return type(self)(-self.real, -self.imag)

    def __sub__(self, other: Any) -> GaussianRational:
        return self + -self.coerce(other)

    def __rsub__(self, other: Any) -> GaussianRational:
        return self.coerce(other) - self

    def __mul__(self, other: Any) -> GaussianRational:
        other = self.coerce(other)
        return type(self)(self.real * other.real - self.imag * other.imag,
                          self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def __truediv__(self, other: Any) -> GaussianRational:
        other = self.coerce(other)
        norm = other.norm_squared()
        if norm == 0:
            raise ZeroDivisionError("division by zero in Q(i)")
        product = self * other.conjugate()
        return type(self)(product.real / norm, product.imag / norm)

    def __rtruediv__(self, other: Any) -> GaussianRational:
        return self.coerce(other) / self

    def __pow__(self, exponent: int) -> GaussianRational:
        if isinstance(exponent, bool) or not isinstance(exponent, int):
            raise TypeError("exact exponent must be an integer")
        if exponent < 0:
            return (ONE / self) ** (-exponent)
        result, base = ONE, self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent >>= 1
        return result

    def conjugate(self) -> GaussianRational:
        return type(self)(self.real, -self.imag)

    def norm_squared(self) -> Fraction:
        return self.real * self.real + self.imag * self.imag

    def bit_length(self) -> int:
        """Largest numerator/denominator bit length, for resource diagnostics."""
        return max(abs(self.real.numerator).bit_length(), self.real.denominator.bit_length(),
                   abs(self.imag.numerator).bit_length(), self.imag.denominator.bit_length())

    def __bool__(self) -> bool:
        return self.real != 0 or self.imag != 0

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, (GaussianRational, int, Fraction)) or isinstance(other, bool):
            return False
        try:
            other = self.coerce(other)
        except (TypeError, ValueError, ZeroDivisionError):
            return False
        return self.real == other.real and self.imag == other.imag

    def __hash__(self) -> int:
        # Respect equality with real int/Fraction values.
        return hash(self.real) if self.imag == 0 else hash((self.real, self.imag))

    def __repr__(self) -> str:
        return f"GaussianRational({self.real!r}, {self.imag!r})"


ZERO = GaussianRational()
ONE = GaussianRational(1)
I = GaussianRational(0, 1)

# Short name useful when transcribing exact matrix formulae.
QI = GaussianRational
