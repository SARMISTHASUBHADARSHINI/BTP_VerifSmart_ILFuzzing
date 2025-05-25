package data_collect

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"regexp"
	"runtime"
)

// Exists returns whether the given file or directory exists or not
func Exists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return true, err
}

// UserHomeDir returns the home directory of current user
func UserHomeDir() string {
	env := "HOME"
	if runtime.GOOS == "windows" {
		env = "USERPROFILE"
	} else if runtime.GOOS == "plan9" {
		env = "home"
	}
	return os.Getenv(env)
}

func WriteStrToPath(s string, p string) error {
	file, err := os.Create(p)
	if err != nil {
		return err
	}
	defer file.Close()

	_, err = fmt.Fprint(file, s)
	if err != nil {
		return err
	}
	return nil
}

func AddUpToVersion(source string) string {
	re := regexp.MustCompile(`pragma\ssolidity\s0`)
	source = re.ReplaceAllString(source, `pragma solidity ^0`)
	return source
}

func MkdirIfNotExist(p string) error {
	if exists, _ := Exists(p); !exists {
		err := os.MkdirAll(p, os.ModePerm)
		if err != nil {
			return err
		}
	}

	return nil
}

func DeleteAndMkdir(p string) error {
	if exists, _ := Exists(p); exists {
		err := os.RemoveAll(p)
		if err != nil {
			return err
		}
	}

	err := os.MkdirAll(p, os.ModePerm)
	if err != nil {
		return err
	}

	return nil
}

func SHA256(s string) string {
	algorithm := sha256.New()
	algorithm.Write([]byte(s))
	return hex.EncodeToString(algorithm.Sum(nil))
}

// CopyFile copies a file from src to dst. If src and dst files exist, and are
// the same, then return success. Otherise, attempt to create a hard link
// between the two files. If that fail, copy the file contents from src to dst.
func CopyFile(src, dst string) (err error) {
	sfi, err := os.Stat(src)
	if err != nil {
		return
	}
	if !sfi.Mode().IsRegular() {
		// cannot copy non-regular files (e.g., directories,
		// symlinks, devices, etc.)
		return fmt.Errorf("CopyFile: non-regular source file %s (%q)", sfi.Name(), sfi.Mode().String())
	}
	dfi, err := os.Stat(dst)
	if err != nil {
		if !os.IsNotExist(err) {
			return
		}
	} else {
		if !(dfi.Mode().IsRegular()) {
			return fmt.Errorf("CopyFile: non-regular destination file %s (%q)", dfi.Name(), dfi.Mode().String())
		}
		if os.SameFile(sfi, dfi) {
			return
		}
	}
	if err = os.Link(src, dst); err == nil {
		return
	}
	err = copyFileContents(src, dst)
	return
}

// copyFileContents copies the contents of the file named src to the file named
// by dst. The file will be created if it does not already exist. If the
// destination file exists, all it's contents will be replaced by the contents
// of the source file.
func copyFileContents(src, dst string) (err error) {
	in, err := os.Open(src)
	if err != nil {
		return
	}
	defer in.Close()
	out, err := os.Create(dst)
	if err != nil {
		return
	}
	defer func() {
		cerr := out.Close()
		if err == nil {
			err = cerr
		}
	}()
	if _, err = io.Copy(out, in); err != nil {
		return
	}
	err = out.Sync()
	return
}
