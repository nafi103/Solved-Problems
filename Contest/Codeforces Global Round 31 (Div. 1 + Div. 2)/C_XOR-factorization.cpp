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
 int msb(int n){
    return 63ll - __builtin_clzll(n);
}
 void solve()
{
    int n, k;
    cin >> n >> k;
    if(k & 1){
        for(int i = 0; i < k; i++){
            cout << n << (i < k - 1 ? " ": "\n");
        }
        return;
    }
    int ans[k], tmp = n, i = 0, _xor = 0;
    for(i = 0; i < k and tmp > 0; i++){
        if(i == k - 1){
            ans[i] = _xor ^ n;
            continue;
        }
        debug(i) debug(_xor)
        int val = n, j = msb(tmp);
        tmp -= (1 << j);
        val -= (1 << j);
        for(int l = j - 1; l >= 0; l--){
            bool condition1 = tmp > (1 << l);
            bool condition2 = ((_xor ^ (1 << l)) & (1 << l)) == (n & (1 << l));
            if(condition1 or condition2){
                val |= (1 << l);
            }
        }
        ans[i] = val;
        _xor = _xor ^ ans[i];
    }
    for(i; i < k; i++)
        ans[i] = n;
    for(int i = 0; i < k; i++)
        cout << ans[i] << (i == k - 1 ? "\n" : " ");
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