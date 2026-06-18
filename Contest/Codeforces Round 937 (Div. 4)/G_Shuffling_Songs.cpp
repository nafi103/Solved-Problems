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
 const int N = (1 << 16) + 10;
int dp[16][N], n;
vector<pair<int,int>> song;
 int f(int last, int mask){
    if(mask == 0)
        return 0;
    int &ans = dp[last][mask];
    if(ans != -1)
        return ans;
    ans = 0;
    for(int i = 0; i < n; i++){
        if(mask & (1 << i) and (song[last].first == song[i].first or song[last].second == song[i].second)){
            ans = max(ans, 1 + f(i , (mask ^ (1 << i))));
        }
    }
    return ans;
}
 void solve()
{
    map<string,int> type, writer;
    cin >> n;
    song.clear();
    song.reserve(n);
    for(int i = 0; i < n; i++){
        int it, iw;
        string t,w;
        cin >> t >> w;
        if(type.count(t) == 0){
            it = sz(type);
            type[t] = sz(type);
        }else{
            it = type[t]; 
        }
        if(writer.count(w) == 0){
            iw = sz(writer);
            writer[w] = sz(writer);
        }else{
            iw = writer[w]; 
        }
        song.push_back({it,iw});
    }
    int r = (1 << n) - 1;
    for(int i = 0; i < n; i++){
        for(int j = 0; j <= r; j++){
            dp[i][j] = -1;
        }
    }
    int ans = 0;
    for(int i = 0; i < n; i ++){
        ans = max(ans, 1 + f(i, (r ^ (1 << i))));
    }
    cout << n - ans << endl;
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