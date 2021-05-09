PWD = $(shell pwd)
TARGET_DIR = $(PWD)/target
CRATE = $(PWD)/../Cargo.lock $(PWD)/../Cargo.toml $(PWD)/../src/lib.rs

.PHONY: all
all: $(TARGET_DIR)/executor $(TARGET_DIR)/libplugin_rust.so $(TARGET_DIR)/libplugin_c.so

.PHONY: clean
clean:
	-rm -rf $(TARGET_DIR)/

$(TARGET_DIR)/executor: executor/src/main.rs executor/Cargo.lock executor/Cargo.toml $(CRATE)
	cd executor && cargo build --target-dir=$(TARGET_DIR)
	cp -ft $(TARGET_DIR)/ $(TARGET_DIR)/debug/executor

$(TARGET_DIR)/libplugin_rust.so: plugin-rust/src/lib.rs plugin-rust/Cargo.lock plugin-rust/Cargo.toml $(CRATE)
	cd plugin-rust && cargo build --target-dir=$(TARGET_DIR)
	cp -ft $(TARGET_DIR)/ $(TARGET_DIR)/debug/libplugin_rust.so

$(TARGET_DIR)/libplugin_c.so: plugin-c/plugin.c
	gcc $< -o $@ -fPIC -shared -pthread

.PHONY: test
test: test-rust test-c

.PHONY: test-rust
test-rust: $(TARGET_DIR)/executor $(TARGET_DIR)/libplugin_rust.so
	$?

.PHONY: test-c
test-c: $(TARGET_DIR)/executor $(TARGET_DIR)/libplugin_c.so
	$?
