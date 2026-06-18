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
 int expo(int a, int b){
    int res = 1;
    while(b){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 int mminvprime(int a){
    return expo(a, mod - 2);
}
 const int N = 2e6 + 10;
int fact[N], ifact[N];
 int nCr(int n, int r){
    if(n < r or n < 0 or r < 0)
        return 0;
    return ((fact[n] * ifact[r]) % mod * ifact[n - r]) % mod;
}
 int calc(int a, int b, int c, int d) {
    return (nCr(a + c - 1, c) * nCr(b + d - 1, d)) % mod;
}
 void solve()
{
    int a, b, c, d, ans = 0;
    cin >> a >> b >> c >> d;
    if(a + b == 0){
        cout << (c == 0 or d == 0) << endl;
        return;
    }
    if(abs(b - a) > 1){
        cout << 0 << endl;
        return;
    }
    if(a <= b)
        ans = calc(a + 1, b, c, d);
    if(b <= a){
        ans = (ans + calc(a, b + 1, c, d)) % mod;
    }
    cout << ans << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
     fact[0] = 1;
    for(int i = 1; i < N; i++)
        fact[i] = (fact[i - 1] * i) % mod;
    ifact[N - 1] = mminvprime(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--)
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
     int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}