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
 const int N = 1e5 + 10;
bool visited[N];
int n, m, color[N];
vector<vector<int>>g(N);
char ch[] = {'r', 'g', 'b'};
  void input(){
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        g[i].clear();
        visited[i] = false;
    }
    for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        v--, u--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
}
 void colorize(){
    queue<int> q;
    q.push(0);
    visited[0] = true;
    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(auto &nbr: g[node]){
            if(!visited[nbr]){
                visited[nbr] = true;
                color[nbr] = (color[node] + 1) % 3;
                q.push(nbr);
            }
        }
    }
}
 void solve1()
{
    input();
    colorize();
    for(int i = 0; i < n; i++){
        cout << ch[color[i]];
    }
    cout << endl;
}
 void solve2(){
    string str;
    int q, n;
    cin >> q;
    while(q--){
        cin >> n >> str;
        set<char> s;
        for(auto &c: str)
            s.insert(c);
        if(sz(s) == 1){
            cout << 1 << endl;
        }else{
            char target = '$';
            if(s.count('r') and s.count('g'))
                target = 'g';
            else if(s.count('r') and s.count('b'))
                target = 'r';
            else
                target = 'b';
            for(int i = 0; i < n; i++){
                if(str[i] == target){
                    cout << i + 1 << endl;
                    break;
                }
            }
        }
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    string str;
    cin >> str;
    bool flag = (str == "first");
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        if(flag)
            solve1();
        else
            solve2();
    }
}