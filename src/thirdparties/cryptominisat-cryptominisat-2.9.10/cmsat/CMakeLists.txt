include_directories(
    ${PROJECT_SOURCE_DIR}
)

add_executable(cryptominisat
    Main.cpp
    Solver.cpp
    SolverDebug.cpp
    SolverMisc.cpp
    Gaussian.cpp
    PackedRow.cpp
    XorFinder.cpp
    MatrixFinder.cpp
    VarReplacer.cpp
#   FindUndef.cpp
    ClauseCleaner.cpp
    RestartTypeChooser.cpp
    FailedLitSearcher.cpp
    Subsumer.cpp
    XorSubsumer.cpp
    StateSaver.cpp
    ClauseAllocator.cpp
    UselessBinRemover.cpp
    OnlyNonLearntBins.cpp
    CompleteDetachReattacher.cpp
    DimacsParser.cpp
    SCCFinder.cpp
    SolverConf.cpp
    ClauseVivifier.cpp
    DataSync.cpp
    BothCache.cpp
)

target_link_libraries(cryptominisat
    ${ZLIB_LIBRARY}
    ${Perftools_LIBRARIES}
    ${MYSQL_LIB}
    rt
)
