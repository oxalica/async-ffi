PWD = $(shell pwd)
TARGET_DIR = $(PWD)/target
CRATE = $(PWD)/../Cargo.lock $(PWD)/../Cargo.toml $(PWD)/../src/lib.rs

.PHONY: all
all: $(TARGET_DIR)/executor_rust $(TARGET_DIR)/executor_c $(TARGET_DIR)/libplugin_rust.so $(TARGET_DIR)/libplugin_c.so

.PHONY: clean
clean:
	-rm -rf $(TARGET_DIR)/

$(TARGET_DIR)/executor_rust: executor-rust/src/main.rs executor-rust/Cargo.toml $(CRATE)
	cd executor-rust && cargo build --target-dir=$(TARGET_DIR)
	cp -ft $(TARGET_DIR)/ $(TARGET_DIR)/debug/executor_rust

$(TARGET_DIR)/libplugin_rust.so: plugin-rust/src/lib.rs plugin-rust/Cargo.toml $(CRATE)
	cd plugin-rust && cargo build --target-dir=$(TARGET_DIR)
	cp -ft $(TARGET_DIR)/ $(TARGET_DIR)/debug/libplugin_rust.so

$(TARGET_DIR)/libplugin_c.so: plugin-c/plugin.c
	gcc $< -o $@ -fPIC -shared -pthread

$(TARGET_DIR)/executor_c: executor-c/main.c
	gcc $< -o $@ -pthread -ldl -std=c11 -Wall -Wextra

.PHONY: test
test: test-rust-rust test-rust-c test-c-rust

.PHONY: test-rust-rust
test-rust-rust: $(TARGET_DIR)/executor_rust $(TARGET_DIR)/libplugin_rust.so
	time $?

.PHONY: test-rust-c
test-rust-c: $(TARGET_DIR)/executor_rust $(TARGET_DIR)/libplugin_c.so
	time $?

.PHONY: test-c-rust
test-c-rust: $(TARGET_DIR)/executor_c $(TARGET_DIR)/libplugin_rust.so
	time $?

# Why do you ever have this case?
# .PHONY: test-c-c
# test-c-c: $(TARGET_DIR)/executor_c $(TARGET_DIR)/libplugin_c.so
#     time $?
