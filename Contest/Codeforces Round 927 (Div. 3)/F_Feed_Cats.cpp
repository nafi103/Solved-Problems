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
 const int N = 1e6 + 10;
int dp[N], mx[N], cnt[N], mxr;
 void initialize(int n){
    for(int i = 1; i <= n; i++){
        mxr = -inf;
        dp[i] = -1;
        mx[i] = i;
        cnt[i] = 0;
    }
}
 int f(int pos){
    if(pos > mxr)
        return 0;
    int &ans = dp[pos];
    if(ans != -1)
        return ans;
    ans = f(pos + 1);
    ans = max(ans, cnt[pos] + f(mx[pos] + 1));
    return ans;
}
 void solve()
{
    int n, m;
    cin >> n >> m;
    initialize(n);
    vector<pair<int,int>> cat(m);
    for(auto &[l,r]: cat){
        cin >> l >> r;
        cnt[l]++;
        cnt[r + 1]--;
        mxr = max(mxr, r);
    }
    sort(all(cat));
    for(int i = 1, p = 0, rmax = 1; i<=mxr; i++){
        while(p < m and cat[p].first <= i){
            rmax = max(rmax, cat[p].second);
            p++;
        }
        mx[i] = max(mx[i], rmax);
    }
    for(int i = 2; i <= mxr; i++){
        cnt[i] += cnt[i - 1];
    }
    cout << f(1) << endl;
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