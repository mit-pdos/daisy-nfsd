# Running eval on AWS

## Create image (AMI) with prepped image

Launch an i3.large using Hirsute

Run `setup-image.sh`

Should only take 2-3 minutes

Stop instance

Select instance and click on Actions > Images and templates > Create image

This takes a while (due to taking a snapshot)

Name image daisy-eval-run

## Run experiments

Boot from AMI - need to set instance type (i3.metal) and security group

Run `aws-setup.sh` first

Run `eval.sh`
