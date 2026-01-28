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

const int N = 3e5 + 10;
bool present[N], visited[N], visited_prime[N];
int s, t, n, spf[N], a[N], d[N], id[N];

void input(){
    for(int i = 0; i < N; i++)
        d[i] = inf;
    cin >> n;
    int tmp;
    for(int i = 1; i <= n; i++){
        cin >> a[i];
        id[a[i]] = i;
        present[a[i]] = true;
    }
    cin >> s >> t;
    id[a[s]] = s;
    id[a[t]] = t;
}

void solve()
{
    input();
    vector<vector<int>> g(N);
    if(s == t){
        cout << 1 << endl;
        cout << s << endl;
        return;
    }
    if(a[s] == 1 or a[t] == 1){
        cout << -1 << endl;
        return;
    }
    if(gcd(a[s], a[t]) != 1){
        cout << 2 << endl;
        cout << s << " " << t << endl;
        return;
    }
    queue<pair<int,int>> q;
    visited[a[s]] = true;
    q.push({a[s], 0});
    while(!q.empty()){
        vector<int> p_factor;
        auto [x, len] = q.front();
        q.pop();
        d[x] = len;
        int save = x;
        if(x == a[t])
            break;
        while(x > 1){
            int p = spf[x];
            while(x % p == 0)
                x /= p;
            p_factor.push_back(p);
        }
        for(auto &p: p_factor){
            if(!visited_prime[p]){
                visited_prime[p] = true;
                for(int j = p; j < N; j+=p){
                    if(!visited[j] and present[j]){
                        visited[j] = true;
                        q.push({j, len + 1});
                        g[save].push_back(j);
                        g[j].push_back(save);
                    }
                }
            }
        }
    }
    if(!visited[a[t]]){
        cout << -1 << endl;
        return;
    }
    vector<int> path;
    path.push_back(a[t]);
    while(path.back() != a[s]){
        for(auto &x: g[path.back()]){
            if(d[x] == d[path.back()] - 1){
                path.push_back(x);
                break;
            }
        }
    }
    reverse(all(path));
    cout << sz(path) << endl;
    for(auto &x: path){
        cout << id[x] << (x == a[t] ? '\n' : ' ');
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    spf[0] = spf[1] = -1;
    for(int i = 1; i < N; i++)
        spf[i] = i;
    for(int i = 2; i * i < N; i++){
        if(spf[i] == i){
            for(int j = i + i; j < N; j+=i)
                spf[j] = min(spf[j], i);
        }
    }
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}