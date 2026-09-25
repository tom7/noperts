#!/bin/bash

make -j difficult229.exe || exit -1

./difficult229.exe --gpu \
        --rand \
        --chart 0 \
        --difficult chart0.difficult \
        --splits_file chart0.single.splits \
        --out_dir . \
        --batch_size 8192 \
        --lp_box_depth 999 \
        --cone_samples 8 \
        --escalate_depth 40 \
        --escalate_cone_samples 12 \
        --deep_escalate_depth 46 \
        --deep_escalate_cone_samples 16 \
        --max_depth 80 \
        --max_box_depth 60 \
        --max_view_depth 20 \
        --limit_sec 3601 \
        --threads 8
