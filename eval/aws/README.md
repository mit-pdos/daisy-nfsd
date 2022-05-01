# Running eval on AWS

## Create image (AMI) with prepped image

Launch an i3.xlarge using Impish
(ubuntu/images-testing/hvm-ssd/ubuntu-impish-daily-amd64-server-20220429). This
is a daily image, so you may need to use a more recent version (the old ones
become unavailable over time). Make
sure to **increase the root volume size to 12GB**.

`wget https://raw.githubusercontent.com/mit-pdos/daisy-nfsd/main/eval/aws/setup-image.sh`

Run `bash setup-image.sh [--no-fscq]`

Will take 5 minutes with `--no-fscq`, 20 minutes if including FSCQ dependencies.

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

Download the results: `rsync -az ubuntu@$ip:./daisy-nfsd/eval/data/ eval/data/aws/`
