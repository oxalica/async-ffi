PWD = $(shell pwd)
BUILD_DIR = $(PWD)/build
TARGET_DIR = $(BUILD_DIR)/target
CRATE = $(PWD)/../Cargo.lock $(PWD)/../Cargo.toml $(PWD)/../src/lib.rs

.PHONY: all
all: build/executor build/libplugin_rust.so build/libplugin_c.so

.PHONY: clean
clean:
	-rm -rf ./build

build/executor: executor/src/main.rs executor/Cargo.lock executor/Cargo.toml $(CRATE)
	cd executor && cargo build --target-dir=$(TARGET_DIR)
	cp $(TARGET_DIR)/debug/executor $(BUILD_DIR)/executor

build/libplugin_rust.so: plugin-rust/src/lib.rs plugin-rust/Cargo.lock plugin-rust/Cargo.toml $(CRATE)
	cd plugin-rust && cargo build --target-dir=$(TARGET_DIR)
	cp $(TARGET_DIR)/debug/libplugin_rust.so $(BUILD_DIR)/libplugin_rust.so

build/libplugin_c.so: plugin-c/plugin.c
	gcc plugin-c/plugin.c -o build/libplugin_c.so -fPIC -shared -pthread

.PHONY: test
test: test-rust test-c

.PHONY: test-rust
test-rust: build/executor build/libplugin_rust.so
	build/executor build/libplugin_rust.so

.PHONY: test-c
test-c: build/executor build/libplugin_c.so
	build/executor build/libplugin_c.so
