.PHONY := rsync


linden.tar: FORCE
	cd ../; git archive -o artifact-vm/$@ popl26_artifact

artifact: linden.tar
	mkdir -p artifact
	tar -x -f linden.tar -C $@

rsync:
	rsync --rsh="ssh -o StrictHostKeyChecking=no -p 2022" \
		--itemize-changes --archive --checksum \
		--include='provision.sh' --include='artifact/***' --exclude='*' \
		./ ubuntu@localhost:/home/ubuntu/Desktop/

autoinstall/user-data: FORCE
	yamllint -d relaxed $@

# In case of issues confirm that /var/lib/cloud/instances/nocloud/user-data.txt
# is present in the VM and check for errors in /var/log/cloud-init-output.log
output/packer/linden.ova: linden.pkr.hcl provision.sh autoinstall/user-data artifact
	packer init $< && packer build $<

output/linden.tar.gz: FORCE provision.sh linden.pkr.hcl autoinstall artifact
	rm -f $@
	tar czf $@ $(filter-out FORCE,$^)

clean:
	rm -fr artifact output linden.tar

vm: output/packer/linden.ova

archive: output/linden.tar.gz

FORCE:
