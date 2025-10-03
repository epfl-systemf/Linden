packer {
  required_plugins {
    virtualbox = {
      version = ">= 1.0.5"
      source  = "github.com/hashicorp/virtualbox"
    }
  }
}

source "virtualbox-iso" "ubuntu" {
  vm_name          = "linden"
  format           = "ova"
  guest_os_type    = "Ubuntu_64"
  output_directory = "output/packer"

  cpus                 = "4"
  memory               = "12288" # 8192
  disk_size            = "65536"
  gfx_controller       = "vmsvga"
  gfx_vram_size        = "32"
  headless             = "false"
  guest_additions_mode = "disable"

  # Useful for debugging
  keep_registered = true
  skip_export     = true

  ssh_username     = "ubuntu"
  ssh_password     = "ubuntu"
  ssh_timeout      = "1h" # Wait long enough for install to complete
  shutdown_command = "sudo systemctl poweroff"
  # pause_before_connecting = "1m" # Wait long enough to reboot (needed on some versions)

  vboxmanage = [
    # Enable port forwarding (2022 → 22)
    ["modifyvm", "{{ .Name }}", "--natpf1", "guest_ssh,tcp,,2022,,22"],
    # Turn of remote desktop environment
    ["modifyvm", "{{ .Name }}", "--vrde", "off"],
  ]

  iso_url      = "https://releases.ubuntu.com/noble/ubuntu-24.04.3-live-server-amd64.iso"
  iso_checksum = "sha256:c3514bf0056180d09376462a7a1b4f213c1d6e8ea67fae5c25099c6fd3d8274b"

  # Automatic Ubuntu installs are configured through a YAML file called `user-data`.
  # The live-server installer looks for it in a drive labeled CIDATA.
  # https://cloudinit.readthedocs.io/en/23.4.1/reference/datasources/nocloud.html
  cd_label = "CIDATA"
  cd_files = ["autoinstall/user-data", "autoinstall/meta-data"]
  boot_command = [
    "<enter><wait1m>", # Start install, wait for autoinstall prompt
    "yes<enter>"       # Confirm autoinstall
  ]
}

build {
  sources = ["source.virtualbox-iso.ubuntu"]

  # Wait for installation to complete
  provisioner "shell" {
    inline  = ["cloud-init status --wait", "mkdir -p Desktop"]
    timeout = "15m"
  }

  # Copy artifact files
  provisioner "file" {
    source      = "artifact"
    destination = "/home/ubuntu/Desktop/"
  }

  # Run the installation script
  provisioner "shell" {
    expect_disconnect = true
    scripts           = ["provision.sh"]
  }
}
