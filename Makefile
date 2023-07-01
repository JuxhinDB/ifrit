IFRIT_IP=192.168.0.11

.PHONY: build push

build-bpf:
	@echo "Building BPF..."
	@echo "$(PWD)"
	@clang -target bpf -Wall -O2 \
		-c ./capsules/ripnet/src/bpf/generic_file_open.bpf.c \
		-o ./capsules/ripnet/src/bpf/generic_file_open.bpf.o

build: build-bpf
	@echo "Building..."
	@cargo b --target=arm-unknown-linux-gnueabihf
	@echo "Done."

push:
	@echo "Pushing..."
	@scp target/arm-unknown-linux-gnueabihf/debug/ifrit root@$(IFRIT_IP):~/ifrit
	@echo "Done."


