# Running eval on AWS

## Create image (AMI) with prepped image

Launch i3.large

Run `bench-vm-setup.sh` (TODO: commit this file)

Should only take 5 minutes

Stop instance

Select instance and click on Actions > Images and templates > Create image

This takes a while (due to taking a snapshot)

Name image daisy-eval-run

## Run experiments

Boot from AMI - need to set instance type (i3.metal) and security group

Run `aws-setup.sh` first (TODO: commit this file)

Run `aws.sh` (TODO: fix this script, unify go-nfsd experimental setup support with
daisy-nfsd)
