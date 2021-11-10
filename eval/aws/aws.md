# Running eval on AWS

## Create image (AMI) with prepped image

Launch an i3.xlarge using Hirsute. Make sure to **increase the root volume size
to 12GB**.

`wget https://raw.githubusercontent.com/mit-pdos/daisy-nfsd/main/eval/aws/setup-image.sh`

Run `bash setup-image.sh`

Will take 20 minutes

Stop instance

Select instance and click on Actions > Images and templates > Create image

Name image daisy-eval-run

This takes several minutes (due to taking a snapshot)

Make sure to deregister old AMI and **delete its snapshot** (this has a monthly
storage cost)

## Run experiments

Boot from AMI - need to set instance type (i3.metal), change to spot instance,
and set security group to something that allows port 22 (for SSH access)

Run `aws-setup.sh` first

Run `eval.sh`
