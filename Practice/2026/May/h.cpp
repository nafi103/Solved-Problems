#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

/****************************************************************/

#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct chash {
    static uint64_t splitmix64(uint64_t x)
    {
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }
    int operator()(int x) const
    {
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};


const int N = 5e4;
unordered_map<int, short, chash> dp[N];
int n, arr[N];
vector<short> _next[N];

int f(int i, int prev){
    if(i == n)
        return 0;
    if(dp[i].find(prev) != dp[i].end()){
        return dp[i][prev];
    }
    int ans = 1, m = sz(_next[i]);
    int l = 0, r = m - 1, start = m;
    while(l <= r){
        int mid = (l + r) / 2;
        if(arr[_next[i][mid]] - arr[i] > prev){
            r = mid - 1;
            start = mid;
        }else{
            l = mid + 1;
        }
    }
    for(int k = start; k < m; k++){
        int j = _next[i][k];
        ans = max(ans, 1 + f(j, arr[j] - arr[i]));
    }
    return dp[i][prev] = ans;
}

void solve()
{
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    for(int j = n - 1; j > 0; j--){
        for(int i = j - 1; i >= 0; i--){
            if(arr[i] < arr[j])
                _next[i].push_back(j);
        }
    }
    for(int i = 0; i < n; i++){
        sort(all(_next[i]), [&](auto &a, auto &b){
            return arr[a] < arr[b];
        });
    }
    int ans = 1, curr = 0, diff = 0;
    for(int i = 0; i < n; i++){
        if(f(i, 0) > ans){
            curr = i;
            ans = f(i, 0);
        }
    }
    cout << ans << endl;
    vector<int> path = {curr + 1};
    for(int j = curr + 1; j < n; j++){
        if(arr[j] > arr[curr] and arr[j] - arr[curr] > diff and dp[j][arr[j] - arr[curr]] == dp[curr][diff] - 1){
            path.push_back(j + 1);
            diff = arr[j] - arr[curr];
            curr = j;
        }
    }
    for(auto &x: path){
        cout << x << " ";
    }
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}