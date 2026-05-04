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
    bool flag = true;
    int n, p, sum = 0;
    cin >> n;
    vector<int> arr(n), brr(n);
    vector<vector<pair<int,int>>> dp(2);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    for(int i =0; i < n; i++){
        cin >> brr[i];
        int diff = brr[i] - arr[i];
        sum += diff;
        if(abs(diff) % 2 != abs(arr[0] - brr[0]) % 2)
            flag = false;
        dp[0].push_back({brr[i] - arr[i], i + 1});
    }
    if(!flag or sum != 0){
        cout <<  -1 << endl;
        return;
    }
    vector<vector<int>> ans;
    for(int z = 0; z < 2 * n + 2; z++){
        dp[1].clear();
        sort(all(dp[0]), [&](pair<int,int> &a, pair<int,int> &b){
            if(a.first != b.first)
                return abs(a.first) > abs(b.first);
            return a.second < b.second;
        });
        auto &next = dp[1];
        if(dp[0][0].first == 0)
            break;
        vector<int> tmp;
        int one = n / 2, neg1 = n / 2;
        for(auto &[val, id]: dp[0]){
            if(val > 0){
                if(one){
                    next.push_back({val - 1, id});
                    tmp.push_back(id);
                    one--;
                }
                else{
                    next.push_back({val + 1, id});
                    neg1--;
                }
            }
            else{
                if(neg1){
                    next.push_back({val + 1, id});
                    neg1--;
                }
                else{
                    next.push_back({val - 1, id});
                    tmp.push_back(id);
                    one--;
                }
            }
        }
        ans.push_back(tmp);
        swap(dp[0], dp[1]);
    }
    cout << sz(ans) << endl;
    for(auto &y: ans){
        int m = sz(y);
        for(int i = 0; i < m; i++)
            cout << y[i] << " \n"[i == m - 1];
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