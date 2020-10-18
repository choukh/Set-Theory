#!/bin/sh

echo "building NatIsomorphism"
coqc -R . ZFC lib/NatIsomorphism.v
echo "building NaturalSubsetMin"
coqc -R . ZFC lib/NaturalSubsetMin.v
echo "building IndexedFamilyUnion"
coqc -R . ZFC lib/IndexedFamilyUnion.v
echo "building EST6_1"
coqc -R . ZFC EST6_1.v
echo "building EST6_2"
coqc -R . ZFC EST6_2.v
echo "building FiniteFacts"
coqc -R . ZFC lib/FiniteFacts.v
echo "building EX6_1"
coqc -R . ZFC EX6_1.v
echo "building EST6_3"
coqc -R . ZFC EST6_3.v
echo "building EST6_4"
coqc -R . ZFC EST6_4.v
echo "building EST6_4_EXTEND_1"
coqc -R . ZFC EST6_4_EXTEND_1.v
echo "building EST6_4_EXTEND_2"
coqc -R . ZFC EST6_4_EXTEND_2.v
echo "building EX6_2"
coqc -R . ZFC EX6_2.v
echo "building EST6_5"
coqc -R . ZFC EST6_5.v
