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
 const int N = 5e3 + 2;
int dp[N][N], a[N], n, m, mx;
vector<pair<int,int>> arr;
 void input(){
    mx = -1;
    arr.clear();
    cin >> n;
    arr.reserve(n);
    for(int i = 0; i < n; i++){
        cin >> a[i];
    }
    sort(a, a + n);
    for(int i = 0, x; i < n; i++){
        x = a[i];
        if(!arr.empty() and arr.back().first == x){
            arr.back().second++;
        }else{
            arr.push_back({x, 1});
        }
    }
    m = sz(arr);
    for(int i = 0; i < m; i++){
        mx = max(mx, arr[i].second);
        for(int j = 0; j <= n; j++)
            dp[i][j] = -1;
    }
}
 int f(int i, int j){
    if(i == m){
        return j >= mx;
    }
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;
    ans = (arr[i].second * f(i + 1, j + arr[i].second)) % mod; // take
    ans = (ans + f(i + 1, j)) % mod; // don't take
    return ans;
}
 void solve()
{
    input();
    cout << f(0, 0) << endl;
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