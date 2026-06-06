#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

int sign[32];

void add(map<vector<int>, int> &mp, vector<int> &arr){
    vector<int> tmp;
    for(int mask = 1; mask < 32; mask++){
        tmp.clear();
        for(int j = 0; j < 5; j++){
            if(mask & (1 << j))
                tmp.push_back(arr[j]);
        }
        mp[tmp]++;
    }
}


int get_ans(map<vector<int>, int> &mp, vector<int> &arr){
    int res = 0;
    vector<int> tmp;
    for(int mask = 1; mask < 32; mask++){
        tmp.clear();
        for(int j = 0; j < 5; j++){
            if(mask & (1 << j))
                tmp.push_back(arr[j]);
        }
        res += sign[mask] * mp[tmp];
    }
    return res - 1;
}

void solve()
{
    map<vector<int>, int> cnt;
    int n;
    cin >> n;
    vector<vector<int>> arr(n,vector<int>(5));
    for(auto &a: arr){
        for(auto &x: a)
            cin >> x;
        sort(all(a));
        add(cnt, a);
    }

    int match = 0;

    for(int i = 0; i < n; i++){
        match += get_ans(cnt, arr[i]);
    }

    match >>= 1;

    cout << (n * (n - 1)) / 2 - match << endl;
}

int32_t main()
{
    freopen("cowpatibility.in", "r", stdin);
    freopen("cowpatibility.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    for(int i = 1; i < 32; i++){
        if(__builtin_popcount(i) & 1)
            sign[i] = 1;
        else
            sign[i] = -1;
    }

    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}