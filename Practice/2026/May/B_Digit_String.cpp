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

// 1 / 3 cannot be before 2. Either remove all 2 after 1 / 3 or remove all 1 and 3 before 2
// remove all 4

void solve()
{
    int ans = 0;
    string str;
    cin >> str;
    int n = sz(str);
    vector<int> arr;
    for(int i = 0; i < n; i++){
        int c = str[i] - '0';
        if(c == 4)
            ans++;
        else
            arr.push_back(c & 1);
    }
    int odd = 0, even = 0;
    n = sz(arr);
    int last_two = n - 1;
    for(int i = 0; i < n; i++){
        if(arr[i] % 2 == 0)
            last_two = i;
    }
    for(int i = 0; i <= last_two; i++){
        if(arr[i] & 1)
            odd++;
        else if(odd)
            even++;
        if(odd <= even){
            ans += odd;
            odd = 0, even = 0;
        }
    }
    ans += even;
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