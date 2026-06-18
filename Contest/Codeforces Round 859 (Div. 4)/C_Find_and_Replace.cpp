#include <bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int arr[26] = {0};
        int n;
        bool flag = true;
        string str;
        cin>>n>>str;
        for (int i = 0; i < n; i++)
        {
            int curr = str[i]-'a';
            if(arr[curr]==0) arr[curr]=i%2+1;
            else{
                if(arr[curr]!=i%2+1){
                    flag = false;
                    break;
                }
            }
        }
        if(flag) cout<<"YES"<<endl;
        else cout<<"NO"<<endl;
    }
}