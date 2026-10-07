import unittest
from fractions import Fraction
from exact_fourier.dyadic import DyadicRow,directional,exact_rows,shear,role_layer,independent_target
from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import Word,KERNEL_C,Call,shear_steps


def qi(row):
    return tuple(QI(Fraction(r,1<<row.exponent),Fraction(i,1<<row.exponent)) for r,i in zip(row.real,row.imag))


class DyadicTests(unittest.TestCase):
    def test_pairs_match_actual_exact_c_word(self):
        for inverse in (False,True):
            row=DyadicRow([1,7,-9,4],[-5,2,8,-3],3)
            old=qi(row)
            directional(row,3,inverse)
            expected=list(old)
            for x,y in ((0,3),(2,1)):
                pair=Word(KERNEL_C,2,(Call((0,1)),)).compile().evaluate([old[x],old[y]])
                if inverse: pair=pair[::-1]
                expected[x],expected[y]=pair
            self.assertEqual(qi(row),tuple(expected))

    def test_logical_shear_matches_compiled_word_and_restores_source(self):
        for num,den in ((1,1),(-1,1),(1,2),(-1,2)):
            target=DyadicRow([1,3],[-4,6],3);source=DyadicRow([7,-5],[2,9],7)
            old_t,old_s=qi(target),qi(source)
            shear(target,source,num,den)
            circuit=Word(KERNEL_C,2,shear_steps(0,1,Fraction(num,den))).compile()
            for j in range(2):
                actual=circuit.evaluate((old_t[j],old_s[j]))
                self.assertEqual(actual,(qi(target)[j],old_s[j]))

    def test_role_layer_agrees_with_c(self):
        rows=[DyadicRow([j+1],[-j],j%3) for j in range(4)]
        old=[qi(r)[0] for r in rows]
        role_layer(rows,2)
        for x,y in ((0,2),(1,3)):
            pair=Word(KERNEL_C,2,(Call((0,1)),)).compile().evaluate([old[x],old[y]])
            self.assertEqual((qi(rows[x])[0],qi(rows[y])[0]),pair)

    def test_walsh_target_matches_independent_direction_product(self):
        initial=exact_rows([[1.,-.125,3.,.5]],[[.25,2.,-.5,1.]])
        images=[1,2,3,0,1]
        program={'projection':{'address_bits':2,'images':images},'metadata':{'include_padding':False}}
        target=independent_target(program,initial)
        direct=[r.copy() for r in initial]
        for mask in images: directional(direct[0],mask)
        self.assertEqual(target,direct)


if __name__=='__main__': unittest.main()
