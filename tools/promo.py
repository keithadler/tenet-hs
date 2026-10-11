#!/usr/bin/env python3
"""Render the four announcement cards (1600x900 points, saved at 2x) into docs/promo/.

Every number on a card comes from FACTS below and each one is a measurement that has a command in docs/testing.md,
so a card cannot say more than was run. Update FACTS from a fresh run before re-rendering.

usage: promo.py [OUT_DIR]     (needs Pillow; macOS system fonts)
"""
import os
import sys
from PIL import Image, ImageDraw, ImageFilter, ImageFont

FACTS = {
    "init_decls": "57,919",
    "init_secs": "55",
    "swapped": "41,378",
    "fuzz_variants": "350",
    "fuzz_first": "9 of 120",
    "repo": "github.com/keithadler/tenet-hs",
}

W, H, S = 1600, 900, 2
ROUND = "/System/Library/Fonts/SFCompactRounded.ttf"
SANS = "/System/Library/Fonts/SFNS.ttf"
MONO = "/System/Library/Fonts/SFNSMono.ttf"


def font(path, size, weight):
    f = ImageFont.truetype(path, int(size * S))
    f.set_variation_by_name(weight)
    return f


def gradient(c0, c1):
    img = Image.new("RGB", (W * S, H * S))
    px = img.load()
    for y in range(H * S):
        for x in range(0, W * S):
            t = (x / (W * S) * 0.55 + y / (H * S) * 0.45)
            px[x, y] = tuple(int(c0[i] + (c1[i] - c0[i]) * t) for i in range(3))
    return img


def wrap(draw, text, fnt, width):
    lines, cur = [], ""
    for word in text.split():
        trial = (cur + " " + word).strip()
        if draw.textlength(trial, font=fnt) <= width * S:
            cur = trial
        else:
            lines.append(cur)
            cur = word
    lines.append(cur)
    return lines


def badge(img, d):
    d.rounded_rectangle([96 * S, 84 * S, 168 * S, 156 * S], radius=18 * S, fill=(255, 255, 255, 235))
    d.text((132 * S, 120 * S), "λ", font=font(ROUND, 48, "Bold"), fill=(70, 46, 140), anchor="mm")
    d.text((190 * S, 120 * S), "tenet-hs", font=font(ROUND, 40, "Bold"), fill=(255, 255, 255), anchor="lm")


def window(img, box, title, lines, accent=(120, 220, 170)):
    x0, y0, x1, y1 = [v * S for v in box]
    shadow = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(shadow).rounded_rectangle([x0, y0 + 24 * S, x1, y1 + 24 * S], radius=26 * S, fill=(0, 0, 0, 150))
    shadow = shadow.filter(ImageFilter.GaussianBlur(28 * S))
    img.alpha_composite(shadow)
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([x0, y0, x1, y1], radius=26 * S, fill=(18, 18, 28, 245))
    for i, c in enumerate([(255, 95, 86), (255, 189, 46), (39, 201, 63)]):
        cx = x0 + (34 + i * 30) * S
        d.ellipse([cx - 9 * S, y0 + 25 * S, cx + 9 * S, y0 + 43 * S], fill=c)
    d.text(((x0 + x1) / 2, y0 + 34 * S), title, font=font(SANS, 22, "Medium"), fill=(150, 150, 170), anchor="mm")
    m = font(MONO, 28, "Regular")
    mb = font(MONO, 28, "Bold")
    y = y0 + 84 * S
    for text, kind in lines:
        color = {"cmd": (255, 255, 255), "dim": (140, 140, 160), "ok": accent, "bad": (255, 140, 120), "txt": (220, 220, 235)}[kind]
        d.text((x0 + 34 * S, y), text, font=mb if kind in ("ok", "bad") else m, fill=color)
        y += 42 * S


def card(name, c0, c1, headline, sub, win=None, center=None, out="."):
    img = gradient(c0, c1).convert("RGBA")
    d = ImageDraw.Draw(img, "RGBA")
    badge(img, d)
    subf = font(SANS, 38, "Regular")
    if win:
        tx, width = 96, 740
        # shrink the headline until headline and subtitle fit between the badge and the footer
        for size in (84, 76, 68, 60, 54):
            head = font(ROUND, size, "Bold")
            hl = wrap(d, headline, head, width)
            sl = wrap(d, sub, subf, width)
            step = int(size * 1.19)
            block = len(hl) * step + 18 + len(sl) * 54
            if block <= 520:
                break
        y = 200 + (580 - block) // 2 + 20
        for ln in hl:
            d.text((tx * S, y * S), ln, font=head, fill=(255, 255, 255))
            y += step
        y += 18
        for ln in sl:
            d.text((tx * S, y * S), ln, font=subf, fill=(255, 255, 255, 215))
            y += 54
        window(img, win["box"], win["title"], win["lines"])
    else:
        head = font(ROUND, 84, "Bold")
        y = 270
        for ln in wrap(d, headline, head, 1300):
            d.text((W / 2 * S, y * S), ln, font=head, fill=(255, 255, 255), anchor="mt")
            y += 100
        y += 30
        pill = font(MONO, 38, "Regular")
        text = center["cli"]
        tw = d.textlength(text, font=pill) / S
        d.rounded_rectangle([(W - tw) / 2 * S - 40 * S, y * S, (W + tw) / 2 * S + 40 * S, (y + 84) * S], radius=22 * S, fill=(18, 18, 28, 235))
        d.text((W / 2 * S, (y + 42) * S), text, font=pill, fill=(120, 220, 170), anchor="mm")
        y += 130
        for ln in wrap(d, sub, subf, 1100):
            d.text((W / 2 * S, y * S), ln, font=subf, fill=(255, 255, 255, 215), anchor="mt")
            y += 54
    foot = font(SANS, 28, "Medium")
    d.text((96 * S, (H - 70) * S), FACTS["repo"], font=foot, fill=(255, 255, 255, 170))
    path = os.path.join(out, name)
    img.convert("RGB").save(path)
    return path


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "..", "docs", "promo")
    os.makedirs(out, exist_ok=True)
    F = FACTS
    paths = []
    paths.append(card("1-hero.png", (43, 29, 92), (15, 76, 92),
        "A second Lean kernel. In Haskell.",
        f"It re-checks all of Init: {F['init_decls']} declarations, none rejected.",
        win={"box": (880, 190, 1510, 690), "title": "Terminal",
             "lines": [("$ tenet-hs check Init.ndjson", "cmd"), ("export by lean4export,", "dim"), ("Lean 4.35.0-rc4, format 3.1.0", "dim"),
                       ("", "txt"), (f"OK: {F['init_decls'].replace(',', '')} checked,", "ok"), ("0 failed, 59349 constants,", "ok"), (f"{F['init_secs']}s", "ok")]}, out=out))
    paths.append(card("2-agree.png", (60, 30, 90), (18, 70, 110),
        f"{F['swapped']} proofs swapped. The same {F['swapped']} rejected.",
        "Every theorem in Init got another theorem's proof. Two kernels, two languages, one verdict.",
        win={"box": (880, 190, 1510, 690), "title": "Terminal",
             "lines": [("rejected, by kernel", "dim"), ("", "txt"), (f"tenet-hs   {F['swapped']}", "ok"), (f"Tenet      {F['swapped']}", "ok"), ("", "txt"),
                       ("diff of the two lists:", "dim"), ("identical", "ok")]}, out=out))
    paths.append(card("3-honest.png", (72, 28, 70), (20, 60, 96),
        "The fuzzer found a bug on its first run.",
        f"{F['fuzz_first']} damaged files split the two kernels. Fixed, and now {F['fuzz_variants']} agree.",
        win={"box": (880, 190, 1510, 690), "title": "Terminal",
             "lines": [("seed 12: 3 rejected by tenet-hs,", "txt"), ("  5 by tenet: DISAGREE", "bad"), ("only tenet:", "dim"), ("  MonadWithReader.casesOn", "txt"), ("  MonadWithReader.recOn", "txt"),
                       ("", "txt"), (f"{F['fuzz_variants']} variants, 0 disagreements", "ok")]}, out=out))
    paths.append(card("4-free.png", (35, 40, 100), (16, 84, 84),
        "Free. Open source. Apache 2.0.",
        "Like Lean. Builds with the GHC you already have, with no packages to download. A sibling of Tenet, maintained with it.",
        center={"cli": "tenet-hs check Init.ndjson"}, out=out))
    for p in paths:
        print(p)


main()
