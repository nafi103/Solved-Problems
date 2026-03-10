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

const int N = 10;
vector<pair<int,int>> arr(N);
vector<int> profit(N);
int n, k;

void input(){
    cin >> n >> k;
    for(int i = 0; i < n; i++)
        cin >> arr[i].first;
    for(int i = 0; i < n; i++)
        cin >> arr[i].second;
    sort(arr.begin(), arr.begin() + n, [&](pair<int,int>&a, pair<int,int>&b){
        if(a.second - a.first != b.second - b.first)
            return a.second - a.first > b.second - b.first;
        return a.first < b.first;
    });
    profit[n] = 0;
    for(int i = n - 1; i >= 0; i--){
        profit[i] = profit[i + 1];
        if(arr[i].first < arr[i].second)
            profit[i] += arr[i].second - arr[i].first;
    }
    debug(arr) debug(profit)
}

void solve()
{
    input();
    if(k == 0){
        cout << profit[0] << endl;
        return;
    }
    multiset<pair<int,int>>s;
    int loss = 0, ans = 0, add = 0;
    for(int i = 0; i < k; i++){
        s.insert(arr[i]);
        loss += arr[i].first;
    }
    debug(s)
    ans = max(ans, profit[k] - loss);
    for(int i = k; i < n; i++){
        if(arr[i].first < (*s.rbegin()).first){
            pair<int,int> tmp = *s.rbegin();
            s.erase(tmp);
            if(tmp.first < tmp.second)
                add += tmp.second - tmp.first;
            loss -= tmp.first;
            loss += arr[i].first;
            s.insert(arr[i]);
        }
        debug(s)
        ans = max(ans, profit[i + 1] - loss + add);
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