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
 const int N = 202;
 int dp[N][2 * N], cake[N], n;
 void input(){
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> cake[i];
    }
    sort(cake, cake + n);
    for(int i = 0; i < n; i++){
        for(int j = 0; j < 2 * n ; j++){
            dp[i][j] = -1;
        }
    }
}
 int f(int i, int t){
    if(i == n - 1)
        return abs(t - cake[i]);
    int &ans = dp[i][t];
    if(ans != -1)
        return ans;
    ans = abs(t - cake[i]);
    int mn = inf;
    if(t < cake[i + 1]){
        for(int tp = t + 1; tp <= cake[i + 1]; tp++){
            mn = min(mn, f(i + 1, tp));
        }
    }else{
        mn = f(i + 1, t + 1);
    }
    ans += mn;
    return ans;
}
 void solve()
{
    input();
    int ans = inf;
    for(int t = 1; t <= cake[0]; t++){
        ans = min(ans, f(0, t));
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