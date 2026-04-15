# VoiceComicFlow
**Production Workbench: From PDF to PSD**

## Overview
A dedicated UI workbench designed to maximize the speed of manual bounding-box drawing and numbering for voice comic (video comic) production. AI (YOLOv8) serves merely as a hover-preview assistant; the core value lies in providing a frictionless interface for rapid, human-driven marking and adjustments.

---

## Visual Feature Guide
*(Note: Screenshots utilize blank pages for copyright compliance, but the tool is compatible with standard PDF manga formats.)*

### 1. Lightning-Fast Manual Marking UI
<img width="852" height="1012" alt="Core Marking Logic" src="https://github.com/user-attachments/assets/35a2b329-c4ab-4204-baa6-36b09554b80d" />

> **Designed for Frictionless Control**
> AI provides baseline frame suggestions only on cursor hover. The user maintains total control to adopt, merge, or manually redraw frames with zero friction.
> - **Facial Preservation (Blank Stamp):** Manually deploy circular "blanking" zones to erase marker lines that overlap with character faces, protecting critical expressions for downstream actors.
> - **Gaya (Crowd) Support:** A dedicated marking system for background atmospheric dialogue, independent of main character lines.

### 2. Project Synchronization
<img width="334" height="133" alt="Project Synchronization" src="https://github.com/user-attachments/assets/08434226-1661-4f20-8324-f3b7cbee9216" />

> **Flexible Page Metadata**
> Bypass physical PDF page constraints (e.g., covers). Open any page, define it as "Page 1 of the main story," and set the precise total page count to match your actual production script.

### 3. Instant Character Setup
<img width="402" height="482" alt="Instant Character Management" src="https://github.com/user-attachments/assets/a6d53a0e-5423-46b5-80a8-cdbcbea2567c" />

> **Zero-Friction Palette Import**
> Instantly build your cast by bulk-importing character names and HEX color codes directly via clipboard from spreadsheets (TSV/CSV).

### 4. Integrated Export Workbench
<img width="502" height="632" alt="Integrated Export Workbench" src="https://github.com/user-attachments/assets/3d0ab226-faf4-429e-bfca-9fd76ad99765" />

> **Foundational Asset Generation**
> One-click generation of the foundational materials required for the next steps in production:
> - **Annotated PDF:** Marked and numbered, ready for script verification and director notations.
> - **Layered PSD:** Separated by character layers for image editing software (GIMP/Photoshop).
> - **CSV Tally:** A statistical breakdown of line counts and page appearances per character.
> *(Note: PDF extraction for specific characters is currently unimplemented).*

### 5. Dynamic Re-indexing (Error Prevention)
<img width="189" height="121" alt="Dynamic Re-indexing Before" src="https://github.com/user-attachments/assets/1e3e57e5-f3aa-4e54-8620-c2469c477155" />
<img width="189" height="121" alt="Dynamic Re-indexing After" src="https://github.com/user-attachments/assets/a0cb1723-0e72-4263-a139-169a441ac7b5" />

> **Automatic Number Shifting**
> Built for rapid edits. If a dialogue stamp is deleted during the process, all subsequent numbers automatically recalculate and shift, completely eliminating human numbering errors.

---

## Why VoiceComicFlow?
- **Manual-First UI Design:** Rather than delegating unreliably to AI, this tool acknowledges that human intervention (adjustments, protecting faces, assigning context) is unavoidable. It is built strictly to minimize the friction and stress of the manual preparation process.

## Quick Start
1. Ensure `characters.csv` is in the root directory.
2. Run `VoiceComicFlow.py`.
3. Select your PDF and begin orchestrating.
