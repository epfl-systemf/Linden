linden.tar: FORCE
	cd ../; tar -cvf artifact-vm/linden.tar --exclude="_build" --exclude="_opam" --exclude="artifact-vm" *

autoinstall/user-data: FORCE
	yamllint -d relaxed $@

# In case of issues confirm that /var/lib/cloud/instances/nocloud/user-data.txt
# is present in the VM and check for errors in /var/log/cloud-init-output.log
output/packer/linden.ova: linden.pkr.hcl provision.sh autoinstall/user-data linden.tar
	packer init $< && packer build $<

clean:
	rm -fr output linden.tar

vm: output/packer/linden.ova

FORCE:
