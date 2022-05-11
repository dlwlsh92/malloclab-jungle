# Malloc lab 시험

- 일주일동안 만들었던 `mm.c` 파일을 제출하고 PR 생성
- `make -f ../Makefile-sub` 를 통해 제대로 구현했는지 테스트
- 리뷰어 배정에 따라 다른 사람의 `mm.c` code를 GitHub의 PR 기능을 이용하여 review
- 리뷰 받은 내용을 보고 설문 작성

## 시험 전 코드 제출 절차

0. 시험 내용 받아오기: C 개발 환경에서 Week05-07 project clone 혹은 pull
    1. 새로운 환경인 경우
    ```sh
    $ git clone https://github.com/SWJungle/P4a-Week05-07.git
    $ cd P4a-Week05-07
    ```

    2. 지난 주에 clone 받은 Week05-07 project에서 계속할 경우
    ```sh
    $ cd P4a-Week05-07
    $ git checkout main
    $ git pull
    ```

1. 제출을 위한 준비: 제출자 전용 dir과 branch 생성
    ```sh
    $ cd Week06                              # Week06 dir로 이동
    $ mkdir ${제출자ID}                      # 제출자 전용 dir 생성
    $ cd ${제출자ID}
    $ git checkout -b week06/${제출자ID}     # 제출자 전용 branch 생성
    $ git push -u origin week06/${제출자ID}  # git push를 위한 사전 작업
    ```
2. `mm.c` 제출: `Week06/${제출자ID}/mm.c` 복사
    - 일주일간 만들었던 `mm.c`를 `Week06/${제출자ID}/mm.c`로 복사 후 다음 명령으로 제출
    ```sh
    $ git add mm.c
    $ git commit -m 'submit mm.c'
    $ git push
    ```
    - `sample_user` directory 처럼 mm.c 하나만 추가되면 됨
    - `sample_user`, `common` directory 안의 내용은 변경하지 않도록 주의
3. 리뷰어를 위한 준비: Pull request
    - https://github.com/SWJungle/P4a-Week05-07 에서 내 branch로 제대로 제출 되었는지 확인
    - `base:main <- compare:week06/${제출자ID}` 방향으로 pull request 생성
    - Pull request 제목에 제출자의 이름을 포함하여 reviewer가 찾기 쉽도록 함
    - comment에 구현 특징 및 특기사항 (예: explicit까지 구현)을 적어
      reviewer가 이해하기 쉽도록 함

## 시험 절차
1. 지정된 리뷰어가 해당 코드를 리뷰
    - GitHub PR (pull request) 기능을 사용하여 line별/전체 review 작성
    - `git fetch --all` 후 `git checkout ${대상 branch}`명령을 통해 제출된 code를 직접 확인할 수 있음
    - `make -f ../Makefile-sub`을 통해 trace를 돌려 볼 수도 있음
    - 단, random trace는 malloclab-jungle project와 다른 내용임
2. 리뷰가 완료되면 'submit review' 버튼을 눌러 리뷰가 완료되었음을 알림
3. 리뷰 받은 코드 주인은 해당 review에 대한 설문지 작성
