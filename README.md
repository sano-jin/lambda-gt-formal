# lambda-gt-formal

> 本リポジトリは，現在進行中かつ未発表の研究に関連する実装を含みます．
> 対応する論文が公開された後，引用情報を追記する予定です．

定理証明支援系 Isabelle を用いて λGT の型システムの健全性の形式証明を行った．

- [STLC.thy](./STLC.thy)
  - 初期検討・比較用の単純型の健全性証明．
  - 700 行弱．
- [LambdaGT_Core.thy](./LambdaGT_Core.thy)
  - 線型含意型なしの λGT の型システムの健全性証明．
  - 3311 行．
    STLC.thy の 4.7 倍程度に収まっている．
- [LambdaGT_LI.thy](./LambdaGT_LI.thy)
  - 線型含意型ありの λGT の型システムの健全性証明．
  - 4789 行．
    STLC.thy の 6.8 倍程度．

How to build:

```bash
isabelle build -D . LambdaGT
```
