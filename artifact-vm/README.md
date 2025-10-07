# Artifact VM image creation

Our VM is automatically generated from a textual description, using a [Packer](https://www.packer.io/) script (Packer is a tool for “images as code”, used to build reproducible VM images, containers, etc.).

## Required hardware

The scripts are designed to run in an Ubuntu x86-64 host OS with at least 16GB of RAM.

## To rebuild the VM automatically

1. [Install VirtualBox](https://www.virtualbox.org/manual/ch02.html)
2. [Install Packer](https://developer.hashicorp.com/packer/install) ≥ v1.10.2, `yamllint` (from `apt` package `yamllint`) and `xorriso` (from `apt` package `xorriso`)
3. Unzip `linden.tar.gz` and navigate to `artifact-vm/`
4. Run `make vm`

The last command will download the Ubuntu 24.04 ISO image, automatically set it up in a fresh VM, and provision the VM by copying our code into it, installing dependencies and code editors with extensions, and compiling our code, leaving you with a brand new VM ready for artifact evaluation. This is the process we used to create the VM on Zenodo.

The entire process should take between 30 minutes and one hour to complete (possibly longer depending on your Internet connection speed). Do not interact with the VM while Packer is running (e.g. when the VM asks whether to continue with autoinstall, Packer will eventually input "yes" by itself).


## Troubleshooting

If you encounter the error `VBoxManage: error: AMD-V is being used by another hypervisor (VERR_SVM_IN_USE).`, disable KVM first before running `make vm`:
```
sudo rmmod kvm_amd # if on AMD
sudo rmmod kvm
```
See https://askubuntu.com/questions/403591/amd-v-is-being-used-by-another-hypervisor-verr-svm-in-use for more details.