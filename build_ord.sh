#!/bin/sh

echo "building Natural"
coqc -R . ZFC lib/Natural.v
echo "building NatIsomorphism"
coqc -R . ZFC lib/NatIsomorphism.v
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
echo "building EX6_2"
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

echo "building EST8_1"
coqc -R . ZFC EST8_1.v
