#!/bin/sh

echo "building EST6_1"
coqc -R . ZFC EST6_1.v
echo "building EST6_2"
coqc -R . ZFC EST6_2.v

