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
 const int N = 2e5 + 10;
int a[N], n, add;
bool visited[N];
 void input(){
    cin >> n;
    for(int i = 1; i <= n; i++){
        cin >> a[i];
        visited[i] = false;
    }
    add = 0;
}
 void solve()
{
    input();
    int operation = 0;
    bool found = false;
    for(int i = 1; i <= n; i++){
        if(visited[i])
            continue;
        set<int> cycle;
        int j = i, cnt = 1;
        bool possible = false;
        while(a[j] != i){
            if(cycle.count(a[j] - 1) or cycle.count(a[j] + 1))
                possible = true;
            cycle.insert(a[j]);
            cnt++;
            visited[j] = true;
            j = a[j];
        }
        if(cycle.count(a[j] - 1) or cycle.count(a[j] + 1))
            possible = true;
        cycle.insert(a[j]);
        visited[j] = true;
        if(!found)
            operation += cnt - 1 - possible;
        else
            operation += cnt - 1;
        if(possible)
            found = true;
    }
    cout << operation + (!found) << endl;
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