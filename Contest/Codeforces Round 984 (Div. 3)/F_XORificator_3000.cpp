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
 int find_xor(int n){
    int xor_1_n = ((n + 1) / 2) & 1;
    for(int i = 1; i < 60 and (1ll << i) <= n; i++){
        int section = (1ll << (i + 1));
        int rem = (n + 1) % section;
        if(rem > (1ll << i) and (rem & 1))
            xor_1_n |= (1ll << i);
    }
    return xor_1_n;
}
 int f(int n, int p, int k){
    int xor_1_n = find_xor(n);
    int bound = (n - k) / (1ll << p);
    int bad_xor = find_xor(bound) << p;
    if((bound + (n >= k)) & 1)
        bad_xor = (bad_xor | k);
    return (xor_1_n ^ bad_xor);
}
 void solve()
{
    int l, r, i, k;
    cin >> l >> r >> i >> k;
    int beautyr = f(r, i, k);
    int beautyl = f(l - 1, i, k);
    cout << (beautyr ^ beautyl) << endl;
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