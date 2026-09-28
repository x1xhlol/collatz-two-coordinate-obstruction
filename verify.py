#!/usr/bin/env python3
"""Freshly rebuild and audit the paper's Lean proofs with pinned dependencies.

Requires Python 3.10+, Git, and Lean 4.27.0 with the pinned mathlib checkout.
Only Python's standard library is used. No historical verification reports are read.
"""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


LEAN_VERSION = "4.27.0"
LEAN_COMMIT = "db93fe1608548721853390a10cd40580fe7d22ae"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_MANIFEST_SHA256 = "6c24676b690a32627317b1d6dd58cf9318d689c5481e1edc53d07c93c892632f"
DEPENDENCY_REVISIONS = {
    "Cli": "55c37290ff6186e2e965d68cf853a57c0702db82",
    "LeanSearchClient": "5ce7f0a355f522a952a3d678d696bd563bb4fd28",
    "Qq": "bd58c9efe2086d56ca361807014141a860ddbf8c",
    "aesop": "cb837cc26236ada03c81837bebe0acd9c70ced7d",
    "batteries": "b25b36a7caf8e237e7d1e6121543078a06777c8a",
    "importGraph": "8f497d55985a189cea8020d9dc51260af1e41ad2",
    "mathlib": "a3a10db0e9d66acbebf76c5e6a135066525ac900",
    "plausible": "009dc1e6f2feb2c96c081537d80a0905b2c6498f",
    "proofwidgets": "c04225ee7c0585effbd933662b3151f01b600e40"
}
SOURCE_SHA256 = {'AffineDifferenceMeasure': 'd7f207b01e2557c3c19758b49921d876df60dc7e25d37841812dcad6d9b3d79a',
 'AffineFamilySynchronization': '9e001bc3b246dde4effe37753b5bb004c846a66e13e7add74c2e472346c37eb6',
 'CollatzAffineProgressions': '5e28d1b0cae1f601d06983fd37b588498ad5d0f691c7c2ed1064db18ec6d4cf1',
 'FinitePatternCoalescence': '86208b374e1df4c1ecbefcd33270853b3b0a3349fdeb0aad854ae22939729087',
 'FinitePatternConvergence': '74ccd96f004198fbd04c6a5283022cb78414fd0351f49bc4c0ad61fc1c30ffb5',
 'OddAffineParameter': '6ca72b4eaa71f9f0f7c061d8d6e6f88e86fff4dd66a0c42ae3ec5d9767b4d209',
 'PositiveProgressionCoalescence': '9f503a2ea7ca75c8dcdfe8b7de95618eb526b5ee5bea8c5bf69bb8c35396d58f',
 'PowerTwoModuloThree': '5be46eeab995b54ccdeea3b662944dec43cdedc05e58e61b537b6a66cfcc5e30',
 'ProgressionConvergenceSpecialization': 'd2082e3c7d94e2fb2b762e80e02b327657b16ba73f2782e3c7aaf9fbc84acd50',
 'CollatzCertificateBridge': '1cbad54373f22b1c194f85548c82a2f80605ce11e38b5fdc51e62622afc5dff5',
 'CollatzCore': '34c4d688780811db45487d9b550fd61cb73e4da02b24ac7e63bba926a3402349',
 'CollatzEvenStrictRank': '11433051ed5be90205e6cd2b0bfdeecf687eaacbe7d1a928f36f4cb5144ee32e',
 'CollatzFiniteSourceSupport': '4c2c156e0192520ca4b09e46a652062b26cbf1fbddb8f7eb6742bd8c71402313',
 'CollatzForwardFiveCover': '5b9c935d4bb38b7015679c51f7b548c00796985ad93b21fe74f4bcfa15310aad',
 'CollatzForwardRealContraction': '2a1df94b41b70c618503f0d24563eaec6455127270d0b53d12b157a43c3b98fd',
 'CollatzForwardRealTwoCoordinateNecessary': 'ed4faea0c2a78da5af454e3bd1c140cc8fa8eccec4d7f0107c82e29bf3d239ca',
 'CollatzForwardRealWordGrowth': 'c092f7be3e514c4c427d22ab4a7089b36dbf88f70ad7054947b18a13334c47a8',
 'CollatzMixedSupport': '348f8355d8ac8aa4a70d3895faca5a0a23f6a6916b9ee973dae089f483a62192',
 'CollatzNaturalAffine': '2e4dd2ec0a4d4cb3c84a415e88c724572baa338884a770f9af4c2d5f36dbe6f2',
 'CollatzOddBlocks': 'd0003c39930da1d95a2a5af73b84aeba8278765e87f52f8154e3f3cab4de16f2',
 'CollatzPositiveWord': 'a4c81bc05b0cfff3f58cfe3438fe535ab25477c40636bb99f2f32121722a91aa',
 'CollatzRankAbovePowers': 'cb3091cbfec67f4865d632b04f62954205fe816179d4c6ba34a6a2a000d93558',
 'CollatzRankGrowth': 'c47f9fa60e78e8b2246d3fc0c135c58786ed01d8966d64d1d57eebae759fdcb0',
 'CollatzRankPositiveOffsets': '6ff1627ac117e94390f76523fd1ae5e18f4d056e038a2634482a17dd78d3fe91',
 'CollatzReversedCertificate': '41c033d10c8c4f65596923f4b06584ff92cc50305e010fe750fb0a6d54a7e713',
 'CollatzReversedNaturalCertificate': '75395ea70e44b0fd2b1987e136670d3f059717f7d20c9d69f6ff209a36964944',
 'CollatzReversedNecessaryConditions': '312b366a2285c7760778bf825f70793488788cd03660d8dbf13bb8f634f67351',
 'CollatzReversedRealAbovePowers': 'a6f9f9b187ea68d940bdd44411c0be7f332625c208d30dd2bdd7ccc1a7edc713',
 'CollatzReversedRealAllReturns': '8f6da3e708f2f0982b88c3269182598dfd996032c75ed6460fd9d29097e1736c',
 'CollatzReversedRealCertificate': 'fbdd7789343547a06ce22d66be707029aa968d8d7a9889d08f979d7af87b5403',
 'CollatzReversedRealCommutatorTwo': 'bb795ff92eebb6615295732123edaeae46b419f569884de0fef94f311b78f533',
 'CollatzReversedRealContraction': '51770eb86d1702357b8f3d486700ce1800d39f1ebe0281cafe5362dc44af70e0',
 'CollatzReversedRealCoordinateSwap': '68e54f9e458e80bd8a180534c3f37355321c50838073ac73d8c1d542fe9610ba',
 'CollatzReversedRealCriticalReadout': 'a4ad6aed3736e846a7f657218c8f33e1fd969ba2e10315bbd33815f8a5513ded',
 'CollatzReversedRealExpanding': '605af29065bb6a016c5258e418252f0904129a7f68d4fcf3be88c4fd9e67e197',
 'CollatzReversedRealExpandingBounds': '70011fcf810b3b30b36b1a70f54617a2b57f3b8ffc8f22df4fc057702d365505',
 'CollatzReversedRealExpandingGrowth': '3c709e596daf3a3ddd97b3521cd4f368021f69865f866002fc3a095866a93a2b',
 'CollatzReversedRealExpandingPrefix': '811de6c234b95e4fab28d8295d5c6acac216feb38eba7662c3cfbb78e08ca267',
 'CollatzReversedRealExpandingSupport': '465e2098af8c749b1115b91fb29b632274f7d00e2b5fd26bae093327e37a2c70',
 'CollatzReversedRealGrowth': 'a14e1152ef7adcde74ab6457b9cb9d98d44b447d0feccd0a3195042f9962ff15',
 'CollatzReversedRealMiddleRank': 'e46ae4b84748046e5f61ffd3f052519c647f9dd72a7e22491f5c62fa26ed2717',
 'CollatzReversedRealMiddleRankExtension': '3fcf59e9941840480ef66a6202791451966063db03d33cf2454a30ced26bfb18',
 'CollatzReversedRealMixedGrowth': 'a1760f93cb8dc6dc109a00ef1fac91819b905415cb959e427ac3e10b689729d7',
 'CollatzReversedRealNonsingularEigen': '47dcb8e263dd1b7ff54e67cebb203dc2dde75ce05cd45d58bde0a368250e504e',
 'CollatzReversedRealOrderedPowers': 'fff3cd745d81ce45c27ef9c473ac81165aa55b3ddc0f6af16f173cc0654f2019',
 'CollatzReversedRealOrderedTwo': '3106cb3aa674acabd1d1d6c9fc0e8fbb5669dade5f047c87cd01980b7d28e898',
 'CollatzReversedRealPositiveOffsets': '3c2a5375b00c26090b8c3dd93e4fac604dc6f29bf7e3bfc39830f6a3413732c9',
 'CollatzReversedRealPositiveWord': '633dfbe2bc56b260650637ca2f7643d21c8027646966b2f64a67b4ac2fb09bc6',
 'CollatzReversedRealPowerContraction': 'fe8e1795cdae8022b19b03c678d10a4f8233541525b802703806a4e6694d91f6',
 'CollatzReversedRealProjectionAlgebra': '6f1edbeed71062f5028b3d8237032643bb6709369c1e0713409d74af4365a9f8',
 'CollatzReversedRealRowContraction': '84afa05dda1ae3256cd5a32bedeb440a4f53ee4f2dd54b378cba82684bba706f',
 'CollatzReversedRealScaledProjection': 'a0edfee5624d1efbb24ab174d9c1e7ba4fb475485220675d13b583a6a1037b8f',
 'CollatzReversedRealSingularBinary': 'f07ca577ebbda61bb641f9f8a3333fd64d43782b5f0a34b713d701067868289b',
 'CollatzReversedRealSource': '137096629127624dcc5488b3e6d264c56b63c8073a4f2f0721f85999eef6ae19',
 'CollatzReversedRealStationaryObstruction': '87922ce36189b88f4a3cfe8afcae4b2f8c5b4d2b195e4e03e27b718e3c8ba7e8',
 'CollatzReversedRealStationaryProfile': '17e7db8fb2045da41d9067aa85cdcb01add0f74d9da2eb84289bc80ea3983165',
 'CollatzReversedRealSupportFamily': '4c642ad0312a8f1e884662a41b66aeddf6843e5e09816ff3e2f16d92fd73dad2',
 'CollatzReversedRealTriangular': '3ed6d293c669fdcc44de3aebc1f4eda4d17d374a616808cc7ec6339770988d02',
 'CollatzReversedRealTriangularContracting': '55275ad8f9d5f615d3af1704e0ced5d7298b172f9b72c0910dd067348b875561',
 'CollatzReversedRealTriangularExpanding': '9916ec22fcceda43445496079ceaf1f2752722b20436b88948607487d8da0c1b',
 'CollatzReversedRealTriangularGrowth': '48a44087d9fac74a352e0fa283768af8167751dafc3092eb63cda9bd95353cff',
 'CollatzReversedRealTriangularNecessity': '06ca82ad5ba1e75b05baf9cb7c7767f117e8b428a4d766028056bf0847a3c130',
 'CollatzReversedRealTriangularPositive': '874e794d3ccfd6cc361efc603e27cca8b3a7a6269a0c814bebdbe00d365fa9af',
 'CollatzReversedRealTriangularPrefix': 'bca15f004c51b2a977a6fc630b930d9f09bbbe891f7bca0295e189fd430bee3d',
 'CollatzReversedRealTriangularReadout': 'c062d4cd537f2a05707dba3c57b67d8690fecf5e2a7ff096c2b5c8a649322b1d',
 'CollatzReversedRealTriangularSubunit': '573e25f369febfabb805cc0dbd45747e385392e70ff74393660546f7a655d517',
 'CollatzReversedRealTriangularSuperunit': '67d25196fc8115d4a802d23cfbbe66dce0d504776d464bbb7ed02d6fc6d90f91',
 'CollatzReversedRealTriangularUnit': 'c35699f6cc66b3810bd59ed3371e8c8eeb7ab8d1917b67dcc8df1753ad1d2da1',
 'CollatzReversedRealTriangularZero': '72fb2e43715b3dea6fbb6e7577bbb73634d8a843db51a5d5e65402df6430d58d',
 'CollatzReversedRealTriangularZeroBasic': '72063a1171d007d009f5bd7de58a938d08f666f49db512c7b41b247526b1b412',
 'CollatzReversedRealTwoCoordinate': 'b7cc9035e073d624fd270f6fbde9f2149a290dd93f238643a65aefe4fe434b71',
 'CollatzReversedRealUnitEigen': '486ff22219491b416b2b3edb2c64102669d2f66dfc1a3c599ceaa60e4156e67f',
 'CollatzReversedRealWeakStationaryObstruction': '8b1254e0f728cdaa0368ea3282203aee685bc384d456a08828df8a4e61d5b296',
 'CollatzSupportFamily': '15d8627821fdbd9f2d842997cc8f4d877ef61ac24ff2660d8cec3abbc0dcea3c',
 'FullTwoBasic': '38d6e8029e7fff5a948aca33ad661b28ed232ac527c3627882eac397cf00780e',
 'FullTwoBoundaryTransfer': '1a245f23727eba60bcb71fb546bb0efa44f93f3f1200991a305fea7f37eff8d3',
 'FullTwoCoordinate': '429785555eecec277248380fe0c2e767c8c7303cf0e2712de29878dda2bd29a0',
 'FullTwoFlip': '549dc990100e249b6e2c86f25f6fc4012a07d16662467addea360de693dce06b',
 'FullTwoLowerForward': '9b79f1aaad7f2ff426fd59df267bd6f56927b631166686a00c98ecb43749849f',
 'FullTwoLowerReversed': '97607cb347243c4b5f4c97443d1759a7d30eb014e91c1c49885afcccdc00d818',
 'FullTwoLowerScalar': '7e82f62bff38fc56b73b9214602b08b7c0802d265ebb8b9f9f2dcd0d395dfaa9',
 'FullTwoLowerScalarReverseShape': '663ebb52d152f50e346e6753375e620f2cd9571baedcca40de71cfb576d6b55d',
 'FullTwoMatrixAggregate': '438e7a8db20a0cf8b359c2d616517bfa0a30fee95491b91688919d024c520eab',
 'FullTwoMatrixBasic': 'd0530708a383c4901b2a200e3e9bd5eafd1dff62546f831bfd70661c4323545a',
 'FullTwoMatrixBinaryProjectionBoundary': 'add65620e8df756f1a536de64b21faa99a53b76761f739ccf9a11af973bc66f9',
 'FullTwoMatrixCommonRankOne': '2ddf055b30363bc7e0610d8aa65b6c5051719b17623acef3b5177dc1c365f486',
 'FullTwoMatrixDeterminants': '4f2d8cedb5eb464394a12136f929824be8e054156cdbfb4ef1cfdaf3dd2f7627',
 'FullTwoMatrixFirstDiagonal': '8bf939cbc68254324bb5e9444a6649c6dcfe01e661a3a068842f0d418a709eef',
 'FullTwoMatrixNonsingular': '5c415fc952177ed7125d2012b3b0b6007743f29256954755b4dadb2ab42bfb48',
 'FullTwoMatrixNonsingularBasic': '89b112f02e72e5d1e3987e305844bfa7aa8677a3c8e4302f400adae02f6144cd',
 'FullTwoMatrixNonsingularBoundary': '2a0e541a127a1c09f8a4f5f95c5e456eb52a551cccb0efb31f8bbccc8f66c4bc',
 'FullTwoMatrixNonsingularShape': 'dd306355a1dab4f002f622ff82bc8bb1e5f8922310344e0288dc1a8816813f43',
 'FullTwoMatrixOrientation': '2a7ec179c2143a3ebf419663f5a295f4da016cd7eb4209e4348defead032ee24',
 'FullTwoMatrixReduction': '967201d0509caa1989310f71fa56e2b10209c7cfb8f8ef64ea0e841b81f80e83',
 'FullTwoMatrixRepeated': 'a5b62c790b6681e994200c1b2b569739e13bc590b36259ad7fef763a2b07a10c',
 'FullTwoMatrixSingular': 'ea47fcfb3942734deb71177b0da72e1c4d131eab984dc0c004e1dafdd9578924',
 'FullTwoMatrixSingularAlgebra': '1236461c62c92a83bd766c374e77a8276a78c596b30012c7d9493ce9f24aa7ef',
 'FullTwoMatrixSingularBinary': 'd787c69d87a6b854d6062eb9364cd51b476d6398efc425ac819347af787257c5',
 'FullTwoMatrixSingularBinaryShape': '980eea136d088a3795aecbbcb4a2e191d26e0528cff8337d6a41cd36b9e4a9a4',
 'FullTwoMatrixSingularEqual': 'b1af51c955ff536db7be59ec3b96cf597695c80f22e448e730a57cee672976a7',
 'FullTwoMatrixSingularSupport': '8bb834ac50076495c16a2ff3702bf623c415455ad4f881c1d1fd255fccea066b',
 'FullTwoMatrixStationary': '931a2324b73d46ccb5dad58a765ee7e740554518d23384c1c6b98d1508c7e798',
 'FullTwoMatrixTranspose': 'fa30e171fc0f3275c9c017170e1d46c31bfee33f1bba223366243035faf4b930',
 'FullTwoMatrixTriangular': '057ad504911f8b836cd8fad87d8a9b992cb2db29fe0999b1cf16cb766160f685',
 'FullTwoNormalize': '6841d99a01dc755f1e2f1eb5dedd8478c4b3a949c78c80b99eaf65765c94e8fe',
 'FullTwoSoundness': '7e97553622f5ebffe692ff3654e5bcdd1011b702bb6973263d44517176565664',
 'FullTwoTriangular': '13bb1a176187e8dc2ef6c203da70a856f2b4825ddcf180ece7bb83f18bb83bc4',
 'FullTwoUpper': '54e819496b12d8f77eae8d271e6f8359659ad975f2d6913bad095fa7d461aab7',
 'FullTwoUpperAffine': '610179098bf811e11f8f1e604bd7bdc8141a6317cc94765f5f5f5a604786a402',
 'FullTwoUpperAlgebra': '911b8f5c1b4965f8d9579b45f190c8dc091bc7629acb4e22f82b0da3ea7e3c51',
 'FullTwoUpperBasic': 'ca5fb73132ef31c9c4390b6e0c5db68dc5766417a8a435cd23ab2ffee29be3a2',
 'FullTwoUpperDegenerate': '9dc8ffce2f8c6dbf9fa4bc941f8d62d879e7d1b9513395da38bb0912aed52c39',
 'FullTwoUpperPositive': '41b508fc64cdeb361425f295b127562948f809b6afcc58d5db886ef566492d32',
 'FullTwoUpperTransfer': 'e7c808988ae6312d4f08b9938bcd6b2b0d4edd84106377efab27718a401c71cd',
 'FullTwoUpperUnit': '1e497943c3ef24c914ba060278073fbedd193647f1c61581991ef84eb105fd9a',
 'FullTwoUpperZero': 'bd153d64d819dcf07581d561da9b8707d90f4253e3aa41148a48ad3b8f241a13',
 'ReversedBinaryPowerClosure': '6f448bb1475e4214a10d4acdac8835d526a559d166c93acfd910e39bca23f281',
 'ReversedPositivePrefixArithmetic': 'c1192ed208b4aa4636ba9bbf95ca4094fdc622cd6d71492a676c27e4d1076d9a',
 'ReversedReadoutEigenrow': '862d43eb60e73fc34db7cb968dab576547a5bf8e5f50980d96fc87567eb3084e',
 'ReversedReadoutIndependence': '691739f8d5094883cb9c2381807e9d75b595daaa4f4e734d513a59f2b3cc0dfd',
 'ReversedRealCoordinateChange': 'e7b67d60be8f6d045384cba9e8ffb9325e835965fb370e7720df4b3104002c46',
 'ReversedRealNormalization': '947bb86b18f46ba0f150437c4a334c79a18b89bbc73b5855eff9381237b23761',
 'ReversedSwapRecurrence': '46cf2c22a17649a8e3c0330bbafcd5a21a0656dec7ec2bcd3beeff5eb17ba695',
 'ReversedTriangularGrowthArithmetic': '8fb97637c66874c1d3a628cc692a97901c150dab00bf7be5e353c6c0b4669397',
 'ReversedTriangularTernaryBounds': '9d4f48531ad89194176b5ff0f517e73d1d05372fbc29eef33823e78094b13393',
 'ReversedTwoDimensionalInvertibleMiddle': '41cde34ba6bdf9d528c1a1ee1b088aa8d21fa62d9355206807558090e4022b32',
 'ReversedTwoDimensionalInvertibleMiddleBasic': '5a3497431b37398808192c3ddbd1c79864cbf130b7f55e1d78def06b3e0eb143',
 'ReversedTwoDimensionalInvertibleMiddleSingular': 'fa8b568a9ec37b77bda2d1efcb730dd2d7f717c4f9be36272b1a628ec87977d1',
 'ReversedTwoDimensionalMiddleRank': '57f608def3f879f4421a05fca79a84d3679b0b25c12f5a4fb169918e660e30ae',
 'ReversedTwoDimensionalMiddleRankExtension': 'c38ac075053bb4e78c36ffd71a51c6d1026e1d212872f6afb313826a99aeaec1',
 'ReversedTwoDimensionalNonsingularEigen': '3d2195a2175a3e94be6d17cac6d1abb476ff0897a1617d022cefe2e59481c24e',
 'ReversedTwoDimensionalNonsingularEigenBasic': '4825ce8b11bffe55aec38edd619661aae0186034984749440cd3cbc6e38a106f',
 'ReversedTwoDimensionalNonsingularEigenShape': 'e78060965b3340092e6d6951c3e55ab57cadb5bdce4e2cfc5ab6094558fed0d6',
 'ReversedTwoDimensionalSwapAlgebra': '27a1ab2ffd726db4a99bbf940b212f5ac238580ef9ab13f647162d9233e9a79b',
 'ReversedTwoDimensionalUnitEigen': 'b39dc2bcf2ed90df7726fa4c144ae50b7ff2e11e2b7effdf331d34652e8c0055',
 'ReversedTwoStepReadout': '95422c78e3028de48a312f42feff82b69222fa1d3aa77815b7bb7d71c1e1ed60',
 'ReversedUpperTriangularRay': 'c0a329e955380ae36684ec6d21d3a213d09fbc8dc1f72a6877b2eb3e306d9a7a'}
TOPS = {'FinitePatternConvergence': {'declarations': {'CollatzPositiveProgression.arbitrarily_long_consecutive_equal_first_hitting_times',
                                               'CollatzPositiveProgression.every_finite_pattern_has_equal_first_hitting_times'},
                              'imports': ['FinitePatternCoalescence',
                                          'ProgressionConvergenceSpecialization']},
 'CollatzForwardRealTwoCoordinateNecessary': {'declarations': {'CollatzResearch.ForwardRealTwoCoordinateNecessary.gaps_zero_of_two_coordinate_bounds',
                                                               'CollatzResearch.ForwardRealTwoCoordinateNecessary.positive_eligible_gap_requires_noncontraction',
                                                               'CollatzResearch.ForwardRealTwoCoordinateNecessary.positive_subeigenrow_of_two_coordinate_bounds'},
                                              'imports': ['CollatzForwardRealContraction',
                                                          'CollatzForwardRealWordGrowth']},
 'CollatzReversedRealTwoCoordinate': {'declarations': {'CollatzResearch.RealTwoCoordinate.no_positive_eligible_offset_gap',
                                                       'CollatzResearch.RealTwoCoordinate.reversed_eligible_offsets_equal',
                                                       'CollatzResearch.RealTwoCoordinate.strict_reversed_two_coordinate_contradiction'},
                                      'imports': ['CollatzReversedRealTriangular',
                                                  'CollatzReversedRealCoordinateSwap']},
 'CollatzReversedRealWeakStationaryObstruction': {'declarations': {'CollatzResearch.RealWeakStationaryObstruction.weak_stationary_profile_excludes_strict'},
                                                  'imports': ['CollatzReversedRealOrderedPowers']},
 'FullTwoCoordinate': {'declarations': {'CollatzResearch.FullTwo.forward_all_gaps_zero',
                                        'CollatzResearch.FullTwo.full_two_coordinate_obstruction',
                                        'CollatzResearch.FullTwo.reversed_all_gaps_zero'},
                       'imports': ['FullTwoTriangular',
                                   'FullTwoMatrixReduction']},
 'FullTwoSoundness': {'declarations': {'CollatzResearch.FullTwoSoundness.admissible_preserves_gap',
                                       'CollatzResearch.FullTwoSoundness.gap_wellFounded',
                                       'CollatzResearch.FullTwoSoundness.weak_rule_gives_gap'},
                      'imports': ['FullTwoBasic']}}
EXPECTED_PUBLIC_DECLARATION_COUNT = 633
EXPECTED_AUDITED_DECLARATION_COUNT = 726
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_]*"
QUALIFIED = IDENTIFIER + r"(?:\." + IDENTIFIER + r")*"
AXIOM_OUTPUT = re.compile(
    r"'(" + QUALIFIED + r")' "
    r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))"
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def lean_code(source):
    """Erase strings and nested comments, preserving line numbers and token boundaries."""
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\":
                if i + 1 >= len(source):
                    raise ValueError("Unterminated Lean string escape")
                result.extend("\n" if c == "\n" else " " for c in source[i:i + 2])
                i += 2
            else:
                quoted = char != '"'
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.extend(" " * (end - i))
            i = end
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif char == '"':
            quoted = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)


def source_inventory(name, data):
    code = lean_code(data.decode("utf-8"))
    if re.search(r"\b(?:sorry|admit|native_decide|axiom|opaque|unsafe)\b", code):
        raise ValueError("Forbidden proof placeholder or declaration in " + name)
    if re.search(r"\b(?:section|private|protected|mutual)\b", code):
        raise ValueError("Unsupported declaration scope in " + name)
    imports = re.findall(r"^import (" + QUALIFIED + r")\s*$", code, re.M)
    if len(imports) != len(re.findall(r"\bimport\b", code)) or len(imports) != len(set(imports)):
        raise ValueError("Unsupported or duplicate import in " + name)
    namespaces, public, definitions, raw_prints = [], [], [], []
    counts = {"namespace": 0, "end": 0, "theorem": 0, "lemma": 0, "def": 0, "print": 0}
    for line in code.splitlines():
        match = re.fullmatch(r"(namespace|end) (" + QUALIFIED + r")\s*", line)
        if match:
            kind, target = match.groups()
            counts[kind] += 1
            if kind == "namespace":
                namespaces.append(target)
            elif not namespaces or namespaces.pop() != target:
                raise ValueError("Unmatched namespace end in " + name)
            continue
        match = re.match(r"(theorem|lemma)\s+(" + QUALIFIED + r")(?=\s|\{|\(|:|$)", line)
        if match:
            kind, target = match.groups()
            if not namespaces:
                raise ValueError("Declaration outside namespace in " + name)
            counts[kind] += 1
            public.append(".".join([*namespaces, target]))
            continue
        match = re.match(r"(?:noncomputable )?def (" + QUALIFIED + r")(?=\s|\{|\(|:|$)", line)
        if match:
            if not namespaces:
                raise ValueError("Definition outside namespace in " + name)
            counts["def"] += 1
            definitions.append(".".join([*namespaces, match.group(1)]))
            continue
        match = re.fullmatch(r"#print axioms (" + QUALIFIED + r")\s*", line)
        if match:
            counts["print"] += 1
            raw_prints.append((".".join(namespaces), match.group(1)))
    if namespaces:
        raise ValueError("Unclosed namespace in " + name)
    for kind in ("namespace", "end", "theorem", "lemma", "def"):
        if counts[kind] != len(re.findall(r"\b" + kind + r"\b", code)):
            raise ValueError("An unsupported " + kind + " command was not inventoried in " + name)
    if counts["print"] != len(re.findall(r"#", code)) or not public:
        raise ValueError("Unsupported diagnostic command or empty declaration inventory in " + name)
    defined = public + definitions
    if len(defined) != len(set(defined)):
        raise ValueError("Duplicate declaration or definition in " + name)
    prints = []
    for namespace, target in raw_prints:
        components = namespace.split(".") if namespace else []
        candidates = [".".join([*components[:size], target])
                      for size in range(len(components), -1, -1)]
        found = next((candidate for candidate in candidates if candidate in defined), None)
        if found is None or found in prints:
            raise ValueError("Unknown or duplicate existing axiom print in " + name + ": " + target)
        prints.append(found)
    return {
        "source_sha256": digest(data), "imports": imports,
        "public_declarations": public, "definitions": definitions,
        "existing_axiom_prints": prints,
        "local_dependencies": [item for item in imports if not item.startswith("Mathlib.")],
    }


def audit_output(output, expected):
    axioms = {}
    for name, entries, no_axioms in AXIOM_OUTPUT.findall(output):
        if name in axioms:
            raise ValueError("Duplicate axiom report: " + name)
        declared = set() if no_axioms else {item.strip() for item in entries.split(",") if item.strip()}
        if not declared <= STANDARD_AXIOMS:
            raise ValueError("Nonstandard axioms: " + name + " " + repr(declared))
        axioms[name] = sorted(declared)
    if set(axioms) != set(expected) or AXIOM_OUTPUT.sub("", output).strip():
        raise ValueError("Wrong axiom coverage or unexpected compiler output:\n" + output)
    return axioms


def compile_module(name, source, output, lean, environment, expected):
    command = [lean, "-j1", "-Dlinter.unusedVariables=false",
               "-Dlinter.unusedSimpArgs=false", "-Dlinter.unnecessarySimpa=false",
               "--root=" + str(source.parent), "-o", str(output), str(source)]
    began = time.monotonic()
    compiled = subprocess.run(command, cwd=source.parent, env=environment, text=True,
                              capture_output=True, timeout=900, check=False)
    record = {
        "command": command, "working_directory": str(source.parent),
        "compiler_exit_code": compiled.returncode, "compiler_stdout": compiled.stdout,
        "compiler_stderr": compiled.stderr, "elapsed_seconds": time.monotonic() - began,
        "source_sha256": sha(source),
    }
    if compiled.returncode or compiled.stderr:
        raise RuntimeError("Lean failed: " + name + "\n" + json.dumps(record, indent=2))
    record["existing_print_declaration_axioms"] = audit_output(compiled.stdout, expected)
    if not output.is_file():
        raise ValueError("Lean did not write a compiled module: " + name)
    record["compiled_module_sha256"] = sha(output)
    return record


def run(arguments, directory):
    result = subprocess.run(arguments, cwd=directory, text=True, capture_output=True,
                            timeout=600, check=False)
    if result.returncode or result.stderr:
        raise RuntimeError(f"Command failed: {arguments!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def audited_revision(directory, expected):
    actual = run(["git", "rev-parse", "HEAD"], directory).strip()
    if actual != expected:
        raise ValueError(f"Unexpected dependency revision in {directory}: {actual}")
    run(["git", "diff", "--exit-code", "HEAD", "--"], directory)
    return actual


def revisions(mathlib, manifest):
    expected = {"mathlib": DEPENDENCY_REVISIONS["mathlib"]}
    for package in manifest["packages"]:
        name = package["name"]
        if (package["type"] != "git" or not re.fullmatch(IDENTIFIER, name)
                or name in expected):
            raise ValueError("Unpinned or duplicate mathlib dependency")
        expected[name] = package["rev"]
    if expected != DEPENDENCY_REVISIONS:
        raise ValueError("The mathlib dependency revisions differ from the embedded pins")
    return {
        name: audited_revision(mathlib if name == "mathlib" else
                               mathlib / ".lake" / "packages" / name, revision)
        for name, revision in expected.items()
    }


def closure(directory):
    sources, inventory, active = {}, {}, set()

    def visit(name):
        if name in active:
            raise ValueError("Cyclic local imports: " + name)
        if name in inventory:
            return
        if name not in SOURCE_SHA256:
            raise ValueError("Unpinned local module: " + name)
        active.add(name)
        data = (directory / (name + ".lean")).read_bytes()
        if digest(data) != SOURCE_SHA256[name]:
            raise ValueError("The published proof source changed: " + name)
        sources[name] = data
        item = source_inventory(name, data)
        for dependency in item["local_dependencies"]:
            visit(dependency)
        active.remove(name)
        inventory[name] = item

    for name, expected in TOPS.items():
        visit(name)
        if (inventory[name]["imports"] != expected["imports"]
                or set(inventory[name]["public_declarations"]) != expected["declarations"]):
            raise ValueError("Unexpected top-level imports or theorems: " + name)
    if sources.keys() != SOURCE_SHA256.keys():
        raise ValueError("The proof closure differs from the embedded source inventory")
    names = [name for item in inventory.values() for name in item["public_declarations"]]
    if len(names) != len(set(names)):
        raise ValueError("A public declaration is repeated across local modules")
    if len(names) != EXPECTED_PUBLIC_DECLARATION_COUNT:
        raise ValueError("The reviewed public declaration count changed")
    defined = names + [name for item in inventory.values() for name in item["definitions"]]
    if len(defined) != len(set(defined)):
        raise ValueError("A declaration or definition repeats across local modules")
    if len(defined) != EXPECTED_AUDITED_DECLARATION_COUNT:
        raise ValueError("The reviewed complete declaration count changed")
    return sources, inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True,
                        help="mathlib checkout at the embedded revision, with dependencies built")
    parser.add_argument("--lake", default="lake", help="Lake executable (default: lake on PATH)")
    parser.add_argument("--build-root", type=Path,
                        help="parent of the temporary build (default: system temporary directory)")
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--report", type=Path,
                        help="new report path (default: verification/rebuild.json)")
    args = parser.parse_args()
    checker = Path(__file__).resolve()
    root = checker.parent
    directory = root / "formal"
    report = (args.report or root / "verification" / "rebuild.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite a report; choose a new path with --report")
    sources, inventory = closure(directory)
    guarded = {"verify.py": (checker, sha(checker))}
    for name, data in sources.items():
        guarded["formal/" + name + ".lean"] = (directory / (name + ".lean"), digest(data))

    mathlib = args.mathlib_root.resolve()
    manifest_path = mathlib / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    if digest(manifest_bytes) != MATHLIB_MANIFEST_SHA256:
        raise ValueError("The mathlib manifest differs from the embedded pin")
    manifest = json.loads(manifest_bytes)
    dependency_revisions = revisions(mathlib, manifest)
    lake = shutil.which(args.lake)
    if lake is None:
        raise ValueError("Lake executable not found: " + args.lake)
    lake = str(Path(lake).absolute())
    guarded["toolchain/lake_launcher"] = (Path(lake), sha(Path(lake)))
    lean = run([lake, "env", "which", "lean"], mathlib).strip()
    if not Path(lean).is_absolute() or not Path(lean).is_file():
        raise ValueError("Lake did not identify an absolute Lean executable")
    guarded["toolchain/lean"] = (Path(lean), sha(Path(lean)))
    version = run([lean, "--version"], mathlib).strip()
    if not re.fullmatch(r"Lean \(version " + re.escape(LEAN_VERSION) +
                        r", [^,]+, commit " + LEAN_COMMIT + r", Release\)", version):
        raise ValueError("Unexpected Lean version: " + version)
    reported_library_path = run([lake, "env", "printenv", "LEAN_PATH"], mathlib).strip()
    library_locations, absent_library_locations = [], []
    for entry in reported_library_path.split(os.pathsep):
        location = Path(entry)
        if not entry or not location.is_absolute():
            raise ValueError("Unexpected Lean library path: " + entry)
        if not location.exists():
            absent_library_locations.append(entry)
            continue
        if not location.is_dir():
            raise ValueError("Lean library path is not a directory: " + entry)
        if any((location / (name + ".olean")).exists() for name in sources):
            raise ValueError("A cached local module could shadow the fresh closure: " + entry)
        library_locations.append(entry)
    library_path = os.pathsep.join(library_locations)
    guarded["mathlib/lake-manifest.json"] = (manifest_path, digest(manifest_bytes))
    before = {label: expected for label, (_, expected) in guarded.items()}
    inventory_bytes = json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode()
    public = sorted(name for item in inventory.values() for name in item["public_declarations"])
    declarations = sorted(set(public) | {name for item in inventory.values()
                                         for name in item["definitions"]} |
                          {name for item in inventory.values()
                           for name in item["existing_axiom_prints"]})
    if len(declarations) != EXPECTED_AUDITED_DECLARATION_COUNT:
        raise ValueError("The generated axiom audit differs from the reviewed inventory")
    audit_name = "PublicationAudit"
    audit_source = ("".join("import " + name + "\n" for name in TOPS) + "\n" +
                    "".join("#print axioms " + name + "\n" for name in declarations))
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-proof-", dir=args.build_root) as temporary:
        build = Path(temporary)
        source_dir, module_dir = build / "sources", build / "modules"
        source_dir.mkdir()
        module_dir.mkdir()
        for name, data in sources.items():
            (source_dir / (name + ".lean")).write_bytes(data)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(module_dir) + os.pathsep + library_path
        pending, running = set(sources), {}
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            while pending or running:
                ready = sorted(name for name in pending
                               if set(inventory[name]["local_dependencies"]) <= builds.keys())
                for name in ready[:args.workers - len(running)]:
                    pending.remove(name)
                    future = pool.submit(
                        compile_module, name, source_dir / (name + ".lean"),
                        module_dir / (name + ".olean"), lean, environment,
                        inventory[name]["existing_axiom_prints"])
                    running[future] = name
                if not running:
                    raise ValueError("The local dependency DAG made no progress")
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    builds[name] = future.result()
                    print(json.dumps({"module": name, "status": "PASS",
                                      "completed": len(builds), "total": len(sources)}), flush=True)
        compiled_before = {name: sha(module_dir / (name + ".olean")) for name in sources}
        if any(compiled_before[name] != builds[name]["compiled_module_sha256"]
               for name in sources):
            raise ValueError("A compiled local module changed before the axiom audit")
        audit_path = source_dir / (audit_name + ".lean")
        audit_path.write_text(audit_source)
        audit = compile_module(audit_name, audit_path, module_dir / (audit_name + ".olean"),
                               lean, environment, declarations)
        for name, data in sources.items():
            if (source_dir / (name + ".lean")).read_bytes() != data:
                raise ValueError("A snapshotted source changed during compilation: " + name)
        if audit_path.read_text() != audit_source:
            raise ValueError("The generated audit source changed during compilation")
        compiled_after = {name: sha(module_dir / (name + ".olean")) for name in sources}
        if compiled_after != compiled_before:
            raise ValueError("A compiled local module changed during the axiom audit")
        audit_compiled_after = sha(module_dir / (audit_name + ".olean"))
        if audit_compiled_after != audit["compiled_module_sha256"]:
            raise ValueError("The compiled axiom audit changed")
    after = {label: sha(path) for label, (path, _) in guarded.items()}
    if after != before:
        raise ValueError("A proof source, verifier, compiler, or manifest changed during checking")
    if revisions(mathlib, manifest) != dependency_revisions:
        raise ValueError("A pinned dependency revision changed during checking")
    if any(Path(entry).exists() for entry in absent_library_locations):
        raise ValueError("An excluded absent library directory appeared during checking")
    if any((Path(entry) / (name + ".olean")).exists()
           for entry in library_locations for name in sources):
        raise ValueError("A cached local module appeared in a dependency library")
    after_sources, after_inventory = closure(directory)
    if after_sources != sources or after_inventory != inventory:
        raise ValueError("The complete source/declaration closure changed during checking")
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "top_modules": list(TOPS),
        "top_declarations": sorted(name for item in TOPS.values() for name in item["declarations"]),
        "module_count": len(sources), "public_declaration_count": len(public),
        "audited_declaration_count": len(declarations),
        "additional_audited_definitions": sorted(set(declarations) - set(public)),
        "inventory": inventory, "inventory_sha256": digest(inventory_bytes),
        "builds": builds, "audit": audit, "generated_audit_source": audit_source,
        "all_public_theorems_and_lemmas_audited": True,
        "all_inventoried_definitions_audited": True,
        "compiled_modules_sha256_before_audit": compiled_before,
        "compiled_modules_sha256_after_audit": compiled_after,
        "compiled_audit_sha256_after": audit_compiled_after,
        "all_compiled_modules_match_before_and_after_audit": True,
        "all_local_dependencies_built_in_fresh_directory": True,
        "all_source_snapshots_match_originals_before_and_after": True,
        "guarded_files_sha256_before": before, "guarded_files_sha256_after": after,
        "verifier_sha256": before["verify.py"],
        "lean_version": version, "lean_executable": lean, "lake_executable": lake,
        "lean_reported_library_path": reported_library_path,
        "excluded_absent_library_directories": absent_library_locations,
        "lean_library_path": library_path, "mathlib_manifest_sha256": digest(manifest_bytes),
        "dependency_revisions": dependency_revisions,
        "parallel_lean_workers": args.workers, "threads_per_lean_worker": 1,
        "sat_solver_calls": 0,
        "scope": (
            "For seven nonnegative real affine maps in two coordinates, each with "
            "first diagonal entry at least one, all eleven weak rules in either "
            "word orientation force all eleven first-coordinate offset gaps to "
            "vanish. Separately, for arbitrary nonnegative real affine maps in "
            "two coordinates without a first-diagonal floor, all eleven reversed "
            "weak rules force offset(D composed with A)=offset(D) and "
            "offset(D composed with B)=offset(D composed with G) at every output "
            "coordinate. Thus neither eligible reversed D-TOP boundary admits "
            "a strictly positive offset gap. This additional result concerns "
            "those two reversed boundaries; it does not assert that all eleven "
            "gaps vanish without the diagonal floor or assert a corresponding "
            "unrestricted forward obstruction. Neither obstruction assumes a "
            "coefficient cap, integrality, invertibility, or triangularity. "
            "Separately, every finite set of natural offsets has arbitrarily "
            "large translates whose shortcut Collatz iterates first reach one "
            "at a common finite time, with equal odd counts. The construction "
            "first coalesces the pattern on one dyadic progression and then "
            "chooses a power-of-two endpoint. This includes consecutive runs "
            "of every length but does not prove convergence from arbitrary "
            "prescribed starting values. "
            "For delta >= 0, admissible maps preserve the fixed-gap relation. "
            "A weak affine comparison with first-coordinate offset gap at least "
            "delta yields that relation on nonnegative vectors. For delta > 0, "
            "the relation is well-founded. These are interpretation obstruction "
            "and soundness theorems. In every finite dimension, the nine forward "
            "weak digit and root comparisons force the observed E-iterate to "
            "dominate floor(n/5) times the sum of the three root gaps. A positive "
            "left subeigenrow of A with multiplier below one forces those gaps "
            "to vanish, giving an explicit noncontraction necessity in two "
            "coordinates. In the reversed system, a positive eligible gap "
            "forces every observed G-power row to be nonzero. Such strictness "
            "is impossible when B=alpha X, G=beta Y, 0<=alpha<beta, X,Y>=0, "
            "r X^n v is uniformly bounded for a positive v, and Y^n v is "
            "eventually stationary. Commutation is not assumed; boundedness "
            "and stationarity are explicit hypotheses. These results do not "
            "prove the Collatz conjecture."
        ),
    }
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "modules": len(sources),
                      "public_declarations": len(public), "audited_declarations": len(declarations),
                      "report_sha256": sha(report), "sat_solver_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
