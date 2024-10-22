#!/usr/bin/env bash

# Rename the pre-push sample file if it exists
if [ -f ".git/hooks/pre-push.sample" ]; then
  mv .git/hooks/pre-push.sample .git/hooks/pre-push
fi

# Copy the content of scripts/pre-push into .git/hooks/pre-push
cp scripts/pre-push.sh .git/hooks/pre-push

# Make the pre-push hook executable
chmod +x .git/hooks/pre-push

echo "Pre-push hook installed."
