#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 4e5 + 10;
int ans[N];
 void solve()
{
    int n, l, r;
    cin >> n >> l >> r;
    ans[1] = 1;
    int pxor = 0, pxorl = 0;
    for(int i = 1, target_xor = 1; i <= n; i++, target_xor ++){
        if(i == r){
            int tx = pxorl;
            ans[i] = tx ^ pxor;
            pxor = ans[i] ^ pxor;
        }else{
            if(target_xor == ans[i - 1])
                target_xor++;
            ans[i] = target_xor ^ pxor;
            pxor = target_xor;
            if(i == l - 1)
                pxorl = pxor;
        }
    }
    for(int i = 1; i <= n; i++){
        cout << ans[i] << (i == n? "\n": " ");
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}