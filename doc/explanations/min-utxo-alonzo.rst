Min-Ada-Value Calculation in Alonzo
===================================

The calculation
#################

There is no longer a ``minUTxOValue`` protocol parameter in Alonzo, it was
deprecated at the end of the Mary era. However, the requirement that each
UTxO must contain an amount of ada that depends on the size of the entry.
The size-dependent minimum ada amount in a UTxO is still referred to as the min-ada-value, and
is now calculated using the Alonzo parameter ``coinsPerUTxOWord``.

The minimum ada value calculation relies on the ``size`` function for determining
the size of a token bundle or a lovelace value, which is described in
the Mary era min-value document.

The formula for the min-ada-value calculation, for a UTxO containing an output ``txout`, is:

``utxoEntrySize (txout) * coinsPerUTxOWord``

where

``utxoEntrySize (txout) = utxoEntrySizeWithoutVal + size (v) + dataHashSize (dh)``

The ``v`` variable is the token bundle inside the ``txout`` output, and
``dh`` is the hash of the datum that is contained in the output. If there is
no datum, the hash is represented by ``Nothing``, and takes up ``0`` space.

Example min-ada-value calculations and current constants
#########################################################

Note that the ``coinsPerUTxOWord`` is a protocol parameter and is subject to
change. The values ``utxoEntrySizeWithoutVal`` and ``dataHashSize (dh)``
are fixed at least for the entire Alonzo era.

The following table gives the values of the constants used in the calculation above.

+------------------------------------------+---------------------+
| Ada-only min-utxo value (in lovelace)    |1,000,000 (1 ada)    |
+------------------------------------------+---------------------+
| ``utxoEntrySizeWithoutVal``              |27                   |
+------------------------------------------+---------------------+
| ``coinsPerUTxOWord`` (in lovelace)       |34,482               |
+------------------------------------------+---------------------+
| ``dataHashSize (dh)``, ``dh = Nothing``  |0                    |
+------------------------------------------+---------------------+
| ``dataHashSize (dh)``, ``dh <> Nothing`` |10                   |
+------------------------------------------+---------------------+

** NO datum hash: **

+---------------------+-----------------+-----------------+-------------------+------------------+------------------+---------------------------------+
|                     | One policyID,   | One policyID,   | One PolicyID,     | Two PolicyIDs,   | Two PolicyIDs,   | Three PolicyIDs,                |
|                     |                 |                 |                   |                  |                  |                                 |
|                     | one 0-character | one 1-character | three 1-character | one 0-character  | one 1-character  | ninety-six 1-character          |
|                     |                 |                 |                   |                  |                  |                                 |
|                     | asset name (i)  | asset name (ii) | asset names (iii) | name (iv)        | name for each (v)| names between them (total) (vi) |
+---------------------+-----------------+-----------------+-------------------+------------------+------------------+---------------------------------+
| size of value       | 11              | 12              | 15                | 16               | 17               | 173                             |
+---------------------+-----------------+-----------------+-------------------+------------------+------------------+---------------------------------+
| ``minUTxO``         | 1,310,316       | 1,344,798       | 1,448,244         | 1,482,726        | 1,517,208        | 6,896,400                       |
+---------------------+-----------------+-----------------+-------------------+------------------+------------------+---------------------------------+
| ``minUTxO`` (in ada)| 1.310316        | 1.344798        | 1.448244          | 1.482726         | 1.517208         | 6.896400                        |
+---------------------+-----------------+-----------------+-------------------+------------------+------------------+---------------------------------+

** WITH datum hash: **

+---------------------+-----------------+--------------------+------------------+
|                     | One policyID,   | One PolicyID,      | Two PolicyIDs,   |
|                     |                 |                    |                  |
|                     | one 0-character | three 32-character | one 0-character  |
|                     |                 |                    |                  |
|                     | asset name (vii)|  asset name (viii) | name (ix)        |
+---------------------+-----------------+--------------------+------------------+
| size of value       | 11              |  26                | 16               |
+---------------------+-----------------+--------------------+------------------+
| ``minUTxO``         | 1,655,136       | 2,172,366          | 1,827,546        |
+---------------------+-----------------+--------------------+------------------+
| ``minUTxO`` (in ada)| 1.655136        |  2.172366          | 1.827546         |
+---------------------+-----------------+--------------------+------------------+


* (i) : ``6 + FLOOR(((1 * 12) + 0 + (1 * 28) + 7)/8, 1) = 11``

* (ii) : ``6 + FLOOR(((1 * 12) + 1 + (1 * 28) + 7)/8, 1) = 12``

* (iii) : ``6 + FLOOR(((3 * 12) + (3*1) + (1 * 28) + 7)/8, 1) = 15``

* (iv) : ``6 + FLOOR(((2 * 12) + 0 + (2 * 28) + 7)/8, 1) = 16``

* (v) : ``6 + FLOOR(((2 * 12) + (1*2) + (2 * 28) + 7)/8, 1) = 17``

* (vi) : ``6 + FLOOR(((96 * 12) + 96 + (3 * 28) + 7)/8, 1) = 173``

* (vii) : ``6 + FLOOR (((1 * 12) + 32 + (1 * 28) + 7) / 8) = 15``

* (viii) : ``6 + FLOOR(((3 * 12) + 96 + (1 * 28) + 7)/8, 1) = 26``

* (ix) : ``6 + FLOOR(((3 * 12) + 96 + (1 * 28) + 7)/8, 1) = 16``
