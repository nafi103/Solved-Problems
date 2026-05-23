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

int n, m, d;

bool check(int machine, vector<pair<int,int>> &arr){
    int i = 0;
    queue<int> q;
    for(int day = 1; day <= m; day++){
        while(i < n and arr[i].first == day){
            q.push(arr[i].first);
            i++;
        }
        if(q.empty())
            continue;
        if(day - q.front() > d)
            return false;
        int p = min(sz(q), machine);
        for(int i = 0; i < p; i++)
            q.pop();
    }
    return true;
}

void solve()
{
    cin >> m >> d >> n;
    vector<pair<int,int>> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i].first;
        arr[i].second = i + 1;
    }
    sort(all(arr));

    int l = 1, r = n;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid, arr)){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    cout << l << endl;
    int machine = l;
    queue<int> q;
    for(int day = 1, i = 0; day <= m; day++){
        while(i < n and arr[i].first <= day){
            q.push(arr[i].second);
            i++;
        }
        int p = min(sz(q), machine);
        for(int i = 0; i < p; i++){
            cout << q.front() << " ";
            q.pop();
        }
        cout << 0 << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}