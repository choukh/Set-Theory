#!/bin/sh

echo "building IndexedFamilyUnion"
coqc -R . ZFC lib/IndexedFamilyUnion.v
echo "building EST6_1"
coqc -R . ZFC EST6_1.v
echo "building EST6_2"
coqc -R . ZFC EST6_2.v
echo "building CH6_1"
coqc -R . ZFC CH6_1.v
