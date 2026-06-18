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
 int nC2(int n){
    if(n < 2)
        return 0;
    return (n * (n - 1)) / 2;
}
 int nC3(int n){
    if(n < 3)
        return 0;
    return (n * (n - 1) * (n - 2)) / 6;
}
 void solve()
{
    int n, ans = 0;
    cin >> n;
    vector<int> cnt(n + 1);
    for(int i = 0, x; i < n; i++){
        cin >> x;
        cnt[x]++;
    }
     for(int i = 1; i <= n; i++){
        ans += nC3(cnt[i]);
         if(i >= 2){
            ans += nC2(cnt[i]) * cnt[i - 1];
            ans += cnt[i] * nC2(cnt[i - 1]);
        }
         if(i >= 3){
            ans += nC2(cnt[i]) * cnt[i - 2];
            ans += cnt[i] * nC2(cnt[i - 2]);
            ans += cnt[i] * cnt[i - 1] * cnt[i - 2];
        }
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
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}