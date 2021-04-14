#!/bin/sh

echo "building ZFC0"
coqc -R . ZFC ZFC0.v
echo "building ZFC1"
coqc -R . ZFC ZFC1.v
echo "building ZFC2"
coqc -R . ZFC ZFC2.v
echo "building ZFC3"
coqc -R . ZFC ZFC3.v
echo "building Essential"
coqc -R . ZFC lib/Essential.v
echo "building EpsilonInduction"
coqc -R . ZFC lib/EpsilonInduction.v

echo "building EST2"
coqc -R . ZFC EST2.v
echo "building EX2"
coqc -R . ZFC EX2.v
echo "building EST3_1"
coqc -R . ZFC EST3_1.v
echo "building EST3_2"
coqc -R . ZFC EST3_2.v
echo "building EST3_3"
coqc -R . ZFC EST3_3.v
echo "building EX3_1"
coqc -R . ZFC EX3_1.v
echo "building EX3_2"
coqc -R . ZFC EX3_2.v
echo "building EST7_1"
coqc -R . ZFC EST7_1.v
echo "building Relation"
coqc -R . ZFC lib/Relation.v
echo "building FuncFacts"
coqc -R . ZFC lib/FuncFacts.v

echo "building EST4_1"
coqc -R . ZFC EST4_1.v
echo "building EST4_2"
coqc -R . ZFC EST4_2.v
echo "building EST4_3"
coqc -R . ZFC EST4_3.v
echo "building EX4"
coqc -R . ZFC EX4.v
echo "building Natural"
coqc -R . ZFC lib/Natural.v
echo "building NatIsomorphism"
coqc -R . ZFC lib/NatIsomorphism.v

echo "building EST5_1"
coqc -R . ZFC EST5_1.v
echo "building EST5_2"
coqc -R . ZFC EST5_2.v
echo "building EST5_3"
coqc -R . ZFC EST5_3.v
echo "building EST5_4"
coqc -R . ZFC EST5_4.v
echo "building EX5"
coqc -R . ZFC EX5.v
echo "building EST5_5"
coqc -R . ZFC EST5_5.v
echo "building EST5_6"
coqc -R . ZFC EST5_6.v
echo "building EST5_7"
coqc -R . ZFC EST5_7.v
echo "building Real"
coqc -R . ZFC lib/Real.v

echo "building EST7_2"
coqc -R . ZFC EST7_2.v
echo "building WosetMin"
coqc -R . ZFC lib/WosetMin.v
echo "building EST7_3"
coqc -R . ZFC EST7_3.v
echo "building EST7_4"
coqc -R . ZFC EST7_4.v

echo "building EST6_1"
coqc -R . ZFC EST6_1.v
echo "building Inj_2n3m"
coqc -R . ZFC lib/algebra/Inj_2n3m.v
echo "building IndexedFamilyUnion"
coqc -R . ZFC lib/IndexedFamilyUnion.v
echo "building Dominate"
coqc -R . ZFC lib/Dominate.v
echo "building Choice"
coqc -R . ZFC lib/Choice.v

echo "building EST7_5"
coqc -R . ZFC EST7_5.v
echo "building EST6_2"
coqc -R . ZFC EST6_2.v
echo "building EX6_1"
coqc -R . ZFC EX6_1.v
echo "building NaturalFacts"
coqc -R . ZFC lib/NaturalFacts.v
echo "building OrdFacts"
coqc -R . ZFC lib/OrdFacts.v

echo "building EST6_3"
coqc -R . ZFC EST6_3.v
echo "building EST6_4"
coqc -R . ZFC EST6_4.v
coqc -R . ZFC EX6_2.v
echo "building EST6_5"
coqc -R . ZFC EST6_5.v
echo "building EST6_6"
coqc -R . ZFC EST6_6.v
echo "building EX6_3"
coqc -R . ZFC EX6_3.v
echo "building Cardinal"
coqc -R . ZFC lib/Cardinal.v

echo "building EX7_1"
coqc -R . ZFC EX7_1.v
echo "building EX7_2"
coqc -R . ZFC EX7_2.v

echo "building Ordinal"
coqc -R . ZFC lib/Ordinal.v
echo "building ZornsLemma"
coqc -R . ZFC lib/ZornsLemma.v

echo "building EST7_6"
coqc -R . ZFC EST7_6.v
echo "building Scott's_Trick"
coqc -R . ZFC lib/ScottsTrick.v
echo "building EX7_3"
coqc -R . ZFC EX7_3.v

echo "building Class"
coqc -R . ZFC lib/Class.v
echo "building LoStruct"
coqc -R . ZFC lib/LoStruct.v
echo "building EST8_1"
coqc -R . ZFC EST8_1.v
echo "building EST8_2"
coqc -R . ZFC EST8_2.v
echo "building EST8_3"
coqc -R . ZFC EST8_3.v
echo "building EST8_4"
coqc -R . ZFC EST8_4.v
echo "building EX8_1"
coqc -R . ZFC EX8_1.v
echo "building EX8_2"
coqc -R . ZFC EX8_2.v
