# Running eval on AWS

## Create image (AMI) with prepped image

Launch an i3.large using Hirsute

`wget https://raw.githubusercontent.com/mit-pdos/daisy-nfsd/main/eval/aws/setup-image.sh`

Run `setup-image.sh`

Should only take 2-3 minutes

Stop instance

Select instance and click on Actions > Images and templates > Create image

This takes a while (due to taking a snapshot)

Name image daisy-eval-run

## Run experiments

Boot from AMI - need to set instance type (i3.metal), change to spot instance,
and set security group

Run `aws-setup.sh` first

Run `eval.sh`
