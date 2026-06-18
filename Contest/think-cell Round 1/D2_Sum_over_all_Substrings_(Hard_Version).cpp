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
 void solve()
{
    int n, total = 0, ans = 0;
    cin >> n;
    string str;
    cin >> str;
    map<int,pair<int,int>> cnt; // last_index, {contribution, number of subarray}
    for(int i = 0; i < n; i++){
        if(str[i] == '0'){
            ans += total;
            cnt[-1] = {cnt[-1].first + 1, cnt[-1].second + 1};
            continue;
        }
        vector<int> ers;
        pair<int,int> add = {1, 1};
        total++;
        for(auto &[last, value]: cnt){
            if(last >= i - 1)
                break;
            ers.push_back(last);
            add.first += (value.first + value.second);
            add.second += value.second;
            total += value.second;
        }
        for(auto &x: ers)
            cnt.erase(x);
        cnt[i + 1] = add;
        ans += total;
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