# Artifact image creation

## Required software

The scripts are designed to run in an Ubuntu host OS with at least 16GB of RAM.

You will need Packer, VirtualBox, xorriso and yamllint.

To install Packer, follow the instructions in https://developer.hashicorp.com/packer/install .

To install VirtualBox, download it from https://www.virtualbox.org/wiki/Linux_Downloads and install the downloaded package.

To install yamllint and xorriso on Ubuntu, run `sudo apt install yamllint xorriso`.

Reboot after installing the software.

## Creating the image

Run `make vm` (with an Internet connection available).

If you encounter the error `VBoxManage: error: AMD-V is being used by another hypervisor (VERR_SVM_IN_USE).`, disable KVM first before running `make vm`:
```
sudo rmmod kvm_amd # if on AMD
sudo rmmod kvm
```
See https://askubuntu.com/questions/403591/amd-v-is-being-used-by-another-hypervisor-verr-svm-in-use for more details.